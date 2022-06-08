#ifdef __GNUC__
#define _POSIX_C_SOURCE 200809L
#else
#define _XOPEN_SOURCE 700
#endif

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <time.h>
#include <pthread.h>
#include <sys/inotify.h>
#include <linux/limits.h>
#include <dirent.h>
#include <libgen.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <fcntl.h>
#include <signal.h>

#define NOTIFY_FLAGS (IN_CREATE | IN_MODIFY | IN_DELETE | IN_MOVE)
#define RESPONSE_PROTOCOL "HTTP/1.1"
#define countof(a) (sizeof(a) / sizeof(*(a)))

typedef struct { char *name, *value; } header_t;
typedef struct {
	pthread_mutex_t mutex;
	struct { char path[PATH_MAX]; } *paths;
	int num;
} watched_t;

typedef struct
{
	char buf[65535];
	const char *protocol;
	const char *method;
	const char *query_string;
	const char *uri;
	header_t headers[17];
} req_t;

const static char g_inject[] =
"<script>(()=>{"
	"var l=location,p=document.currentScript,r='resource'"
	",s=new WebSocket('ws://'+l.host)"
	",b=e=>e.forEach(w=>s.send(w))"
	",t=e=>e.getEntriesByType(r)"
		".map(v=>(v.name.match('^'+l+'(.*)')||[])[1]).filter(v=>v);"
	"s.onopen=e=>{"
		"b([...t(performance),'%s']);"
		"new PerformanceObserver(e=>b(t(e))).observe({entryTypes:[r]})"
	"};"
	"s.onmessage=e=>l.reload();"
	"p.parentNode.removeChild(p)"
"})()</script>";

#define A "application/"
#define I "image/"
#define V "video/"
#define U "audio/"
#define T "text/"
static struct { char mime[30]; char ext[7]; } g_mimes[] = {
	{V"3gpp2","3g2"},{U"ogg","oga"},{U"wav","wav"},{A"xhtml+xml","xhtml"},
	{V"webm","webm"},{V"ogg","ogv"},{A"gzip","gz"},{T"javascript","js"},
	{"font/ttf","ttf"},{A"rtf","rtf"},{A"x-sh","sh"},{A"x-freearc","arc"},
	{A"zip","zip"},{U"midi","mid"},{U"mpeg","mp3"},{"font/woff2","woff2"},
	{T"calendar","ics"},{I"png","png"},{I"tiff","tif"},{I"jpeg","jpeg"},
	{V"mp2t","ts"},{A"pdf","pdf"},{U"webm","weba"},{A"x-abiword","abw"},
	{A"xml","xml"},{U"aac","aac"},{V"3gpp","3gp"},{A"ld+json","jsonld"},
	{V"mpeg","mpeg"},{"font/otf","otf"},{A"x-cdf","cda"},{T"html","htm"},
	{A"json","json"},{V"x-msvideo","avi"},{I"gif","gif"},{T"csv","csv"},
	{T"html","html"},{U"midi","midi"},{U"opus","opus"},{I"tiff","tiff"},
	{T"css","css"},{I"x-icon","ico"},{"font/woff","woff"},{I"jpeg","jpg"},
	{V"mp4","mp4"},{T"plain","txt"},{A"msword","doc"},{I"svg+xml","svg"},
	{A"x-bzip2","bz2"},{A"x-csh","csh"},{I"bmp","bmp"},{A"x-bzip","bz"},
	{I"avif","avif"},{I"webp","webp"},{A"ogg","ogx"},{A"epub+zip","epub"},
	{T"javascript","mjs"},{A"x-httpd-php","php"},{A"x-7z-compressed","7z"},
	{A"x-tar","tar"},{A"java-archive","jar"},{A"x-shockwave-flash","swf"}
};

static const char *
get_mime(const char *path)
{
	const char *dot = strrchr(path, '.');

	if (dot) {
		int i;
		++dot;
		for (i = 0; i < sizeof(g_mimes) / sizeof(*g_mimes); ++i)
			if (!strcmp(dot, g_mimes[i].ext))
				return g_mimes[i].mime;
	}

	return "application/octet-stream";
}

static void
sha1(uint8_t *data, size_t n, uint32_t *digest)
{
	const uint64_t bits = n * 8;
	uint32_t hash[] = {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0};
	uint32_t i;
	uint32_t *d;
#define big_endian(val) \
 ( (((val) >> 56) & (0xFFL <<  0)) | (((val) >> 40) & (0xFFL <<  8)) | \
   (((val) >> 24) & (0xFFL << 16)) | (((val) >>  8) & (0xFFL << 24)) | \
   (((val) <<  8) & (0xFFL << 32)) | (((val) << 24) & (0xFFL << 40)) | \
   (((val) << 40) & (0xFFL << 48)) | (((val) << 56) & (0xFFL << 56)) )

	data[n++] = 0x80;
	while ((n + sizeof(uint64_t)) % 64)
		data[n++] = 0;
	*((uint64_t*)(data+n)) = big_endian(bits);
	n += sizeof(uint64_t);

	for (d = (uint32_t*)data; d < (uint32_t*)(data + n);) {
#define rotate(value, bits) (((value) << (bits)) | ((value) >> (32 - (bits))))
		uint32_t a[5];
		uint32_t w[80];
		uint32_t word;

		for (word = 0; word < 16; word++)
			w[word] = htonl(*(d++));
		for (word = 16; word < 32; word++)
			w[word] = rotate((w[word - 3] ^ w[word - 8] ^ w[word - 14] ^ w[word - 16]), 1);
		for (word = 32; word < 80; word++)
			w[word] = rotate((w[word - 6] ^ w[word - 16] ^ w[word - 28] ^ w[word - 32]), 2);

		for (i = 0; i < 5; ++i)
			a[i] = hash[i];

		for (i = 0; i < 80; i++) {
			uint32_t temp;
			uint32_t f = 0;
			uint32_t k = 0;

			if (i <= 19) {
				f = (a[1] & a[2]) | ((~a[1]) & a[3]);
				k = 0x5A827999;
			} else if (i >= 20 && i <= 39) {
				f = a[1] ^ a[2] ^ a[3];
				k = 0x6ED9EBA1;
			} else if (i >= 40 && i <= 59) {
				f = (a[1] & a[2]) | (a[1] & a[3]) | (a[2] & a[3]);
				k = 0x8F1BBCDC;
			} else if (i >= 60 && i <= 79) {
				f = a[1] ^ a[2] ^ a[3];
				k = 0xCA62C1D6;
			}
			temp = rotate(a[0], 5) + f + a[4] + k + w[i];
			a[4] = a[3];
			a[3] = a[2];
			a[2] = rotate(a[1], 30);
			a[1] = a[0];
			a[0] = temp;
		}
		for (i = 0; i < 5; ++i)
			hash[i] += a[i];
	}
	for (i = 0; i < 5; i++)
		digest[i] = ntohl(hash[i]);
}

static void
base64(const uint8_t *src, size_t len, char *dst)
{
	static const unsigned char t[66] =
		"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=";
	const uint8_t *i, *e = (uint8_t*)(src + len);
	for (i = src; i < e; i += 3) {
		*dst++ = t[i[0] >> 2];
		*dst++ = t[(i[0] << 4 & 060) | (i+1 < e ? i[1] >> 4 : 0)];
		*dst++ = t[i+1 < e ? (i[1] << 2 & 074) | (i+2 < e ? i[2] >> 6 : 0) : 64];
		*dst++ = t[i+2 < e ? i[2] & 077 : 64];
	}
	*dst = '\0';
}

static void
websocket_key(const char *key, char *out)
{
	char buffer[512];
	uint32_t digest[5];
	sprintf(buffer, "%s258EAFA5-E914-47DA-95CA-C5AB0DC85B11", key);
	sha1((uint8_t*)buffer, strlen(buffer), digest);
	base64((uint8_t*)digest, sizeof(digest), out);
}

static int
send_file_header(const char *file_name, int *inject)
{
	struct stat buffer;
	int exists;

	if (file_name[0] == '/' || file_name[0] == '\\' || file_name[0] == '.')
		return 0;

	if ((exists = (stat(file_name, &buffer) == 0))) {
		const char *mime = get_mime(file_name);
		size_t length = buffer.st_size;
		if (!strcmp(mime, "text/html")) {
			*inject = 1;
			length += sizeof(g_inject) - 1;
			length += (strlen(file_name) - (sizeof("%s") - 1));
		}
		printf(RESPONSE_PROTOCOL " 200 OK\n");
		printf("Content-Type: %s\n", mime);
		printf("Content-Length: %ld\n", length);
		printf("Last-Modified: %ld\n", buffer.st_mtime * 1000 + buffer.st_mtim.tv_nsec / 1000000);
		printf("\n");
	}
	return exists;
}

static int
send_file(const char *file_name, int inject)
{
	char buf[1024];
	FILE *file;
	size_t nread;
	int err = 1;
	if ((file = fopen(file_name, "rb"))) {
		while ((nread = fread(buf, 1, sizeof(buf), file)) > 0)
			fwrite(buf, 1, nread, stdout);
		err = ferror(file);
		fclose(file);
		if (inject)
			printf(g_inject, file_name);
	}
	return err;
}

static void
send_client(const char *message)
{
	int l = strlen(message);
	char b0 = 0, b1 = 0;
	b0 |= 1 << 7;  /* fin */
	b0 |= 0 << 4;  /* rsv */
	b0 |= 1;       /* opcode */
	if(l <= 125)
		b1 |= l;
	else
		fprintf(stderr, "oh no\n");

	fwrite(&b0, 1, 1, stdout);
	fwrite(&b1, 1, 1, stdout);
	fwrite(message, 1, l, stdout);
	fflush(stdout);
}

static void
parce_receive(const char *buf, uint32_t buf_size, char *out)
{
	int n;
	uint32_t length;
	const char *masks, *data;
	const int fin =   (buf[0] & 0x80) >> 7;
	const int opcode = buf[0] & 0x0f;
	if (opcode != 0x1) /* text */
		return;

	if (fin != 1) /* longer messages not supported */
		return;

	length = buf[1] & 127;
	if (length == 126) {
		masks = &buf[4];
	} else if (length == 127) {
		masks = &buf[10];
	} else {
		masks = &buf[2];
	}
	data = (masks + 4);

	for (n = 0; n < length; ++n)
		out[n] = data[n] ^ masks[n % 4];
	out[n] = '\0';
}

typedef struct {
	int wd;
	char path[PATH_MAX];
} inotify_watched_dir_t;

static void*
websocket_listen(void *arg)
{
	watched_t *watched = arg;
	int num_read;
	char buf[PATH_MAX];
	char path[PATH_MAX] = "";
	while ((num_read = recv(fileno(stdout), buf, sizeof(buf), 0)) > 0) {
		parce_receive(buf, num_read, path);
		pthread_mutex_lock(&watched->mutex);
		watched->paths = realloc(watched->paths, (watched->num + 1) * sizeof(*watched->paths));
		strcpy(watched->paths[watched->num++].path, path);
		pthread_mutex_unlock(&watched->mutex);
	}
	exit(0);
}

static int
is_watched(watched_t *watched, const char *fname)
{
	int i;
	pthread_mutex_lock(&watched->mutex);
	for (i = 0; i < watched->num; ++i)
		if (!strcmp(fname, watched->paths[i].path))
			return 1;
	pthread_mutex_unlock(&watched->mutex);
	return 0;
}

static void
path_from_inotify_event(const struct inotify_event *event, char *fullpath,
                        const inotify_watched_dir_t *inotify_dirs,
                        int inotify_dirs_num)
{
	int i;
	fullpath[0] = '\0';
	for (i = 0; i < inotify_dirs_num; ++i) {
		if (inotify_dirs[i].wd == event->wd) {
			strcpy(fullpath, inotify_dirs[i].path + (sizeof(".") - 1));
			break;
		}
	}
	if (strlen(fullpath) > 0)
		strcat(fullpath, "/");
	strcat(fullpath, event->name);
}

static void
inotify_add_dir(char *base_path, int inotify_fd,
                inotify_watched_dir_t **inotify_dirs, int *inotify_dirs_num)
{
	char path[1000];
	struct dirent *dp;
	DIR *dir = opendir(base_path);

	if (!dir)
		return;

	(*inotify_dirs) = realloc(*inotify_dirs, (*inotify_dirs_num + 1) * sizeof(**inotify_dirs));
	(*inotify_dirs)[*inotify_dirs_num].wd = inotify_add_watch(inotify_fd, base_path, NOTIFY_FLAGS);
	strcpy((*inotify_dirs)[*inotify_dirs_num].path, base_path);
	++*inotify_dirs_num;

	while ((dp = readdir(dir)) != NULL) {
		if (dp->d_name[0] != '.') {
			strcpy(path, base_path);
			strcat(path, "/");
			strcat(path, dp->d_name);
			inotify_add_dir(path, inotify_fd, inotify_dirs, inotify_dirs_num);
		}
	}
	closedir(dir);
}

static int
add_inotify_watches(inotify_watched_dir_t **inotify_dirs, int *inotify_dirs_num)
{
	int inotify_fd = inotify_init();
	if (inotify_fd < 0)
		perror("inotify_init");
	inotify_add_dir(".", inotify_fd, inotify_dirs, inotify_dirs_num);
	return inotify_fd;
}

static void
websocket(const char *key)
{
	int i, n;
	char out[128] = {0};
	pthread_t websocket_listen_thr;
	char inotify_buf[10 * sizeof(struct inotify_event) + PATH_MAX + 1];
	int inotify_fd;
	watched_t watched;
	inotify_watched_dir_t *inotify_dirs = NULL;
	int inotify_dirs_num = 0;

	websocket_key(key, out);
	printf(RESPONSE_PROTOCOL " 101 Switching Protocols\n");
	printf("Upgrade: websocket\n");
	printf("Connection: Upgrade\n");
	printf("Sec-WebSocket-Accept: %s\n\n", out);
	fflush(stdout);

	inotify_fd = add_inotify_watches(&inotify_dirs, &inotify_dirs_num);

	if (pthread_mutex_init(&watched.mutex, NULL) != 0) {
		fprintf(stderr, "mutex init has failed\n");
		exit(1);
	}

	pthread_create(&websocket_listen_thr, NULL, &websocket_listen, &watched);

	while ((n = read(inotify_fd, inotify_buf, sizeof(inotify_buf))) > 0) {
		char *p = inotify_buf;
		while (p < inotify_buf + n) {
			struct inotify_event *event = (struct inotify_event*)p;
			char path[PATH_MAX];
			path_from_inotify_event(event, path, inotify_dirs, inotify_dirs_num);
			if (((event->mask & NOTIFY_FLAGS) != 0) && is_watched(&watched, path)) {
				send_client("reload");
				goto end;
			}
			p += sizeof(struct inotify_event) + event->len;
		}
	}
end:
	for (i = 0; i < inotify_dirs_num; ++i)
		inotify_rm_watch(inotify_fd, inotify_dirs[i].wd);
	free(inotify_dirs);
	free(watched.paths);
	close(inotify_fd);
}

static void
parse_http(int client, req_t *req)
{
	int rcvd;
	char *query_string, *uri;
	header_t *h;
	memset(req, 0, sizeof(*req));

	rcvd = recv(client, req->buf, sizeof(req->buf), 0);
	if (rcvd < 0) {
		fprintf(stderr,("recv() error\n"));
		exit(1);
	}
	if (rcvd == 0) {
		fprintf(stderr,"Client disconnected upexpectedly.\n");
		exit(0);
	}
	req->buf[rcvd] = '\0';

	req->method   = strtok(req->buf,  " \t\r\n");
	uri           = strtok(NULL, " \t");
	req->protocol = strtok(NULL, " \t\r\n"); 

	if ((query_string = strchr(uri, '?')))
		*query_string++ = '\0';
	else
		query_string = uri - 1;

	req->uri = uri;
	req->query_string = query_string;

	for (h = req->headers; h < req->headers + countof(req->headers); ++h) {
		char *k,*v,*t;
		k = strtok(NULL, "\r\n: \t");
		if (!k) break;
		v = strtok(NULL, "\r\n");
		while(*v && *v == ' ')
			v++;
		h->name  = k;
		h->value = v;
		t = v + 1 + strlen(v);
		if (t[1] == '\r' && t[2] == '\n') break;
	}
}

static int
http(const char *port, req_t *req)
{
	int err;
	int listenfd;
	struct sockaddr_in clientaddr;
	struct addrinfo hints, *res, *p;

	printf("Hosting %shttp://127.0.0.1:%s%s\n", "\033[92m",port,"\033[0m");

	memset (&hints, 0, sizeof(hints));
	hints.ai_family = AF_INET;
	hints.ai_socktype = SOCK_STREAM;
	hints.ai_flags = AI_PASSIVE;
	err = getaddrinfo( NULL, port, &hints, &res);
	if (err) {
		perror ("getaddrinfo() error");
		return err;
	}
	for (p = res; p != NULL; p = p->ai_next) {
		int option = 1;
		listenfd = socket(p->ai_family, p->ai_socktype, 0);
		setsockopt(listenfd, SOL_SOCKET, SO_REUSEADDR, &option, sizeof(option));
		if (listenfd == -1) continue;
		if (bind(listenfd, p->ai_addr, p->ai_addrlen) == 0) break;
	}
	if (p == NULL) {
		perror ("socket() or bind()");
		return -1;
	}

	freeaddrinfo(res);

	err = listen(listenfd, 16);
	if (err) {
		perror("listen() error");
		return err;
	}

	signal(SIGCHLD, SIG_IGN);
	while (1) {
		int client;
		socklen_t addrlen;

		addrlen = sizeof(clientaddr);
		client = accept(listenfd, (struct sockaddr *) &clientaddr, &addrlen);

		if (client<0) {
			perror("accept() error");
			continue;
		}

		if (fork() == 0) {
			close(listenfd);
			parse_http(client, req);
			dup2(client, STDOUT_FILENO);
			return 0;
		} else {
			close(client);
		}
	}
	return 1;
}

static const char*
request_header(const req_t *req, const char* name)
{
	const header_t *h;
	for (h = req->headers; h->name; ++h)
		if (strcmp(h->name, name) == 0)
			return h->value;
	return NULL;
}

int
main(int argc, char *argv[])
{
	req_t req;
	if (http(argc > 1 ? argv[1] : "8080", &req) == 0) {
		const char *upgrade = request_header(&req, "Upgrade");
		if (upgrade && !strcmp(upgrade, "websocket")) {
			const char *key = request_header(&req, "Sec-WebSocket-Key");
			websocket(key);
		} else {
			int inject = 0;
			const char *file = strlen(req.uri) - 1 ? req.uri + 1 : "index.html";
			if (send_file_header(file, &inject)) {
				send_file(file, inject);
			} else {
				printf(RESPONSE_PROTOCOL " 404 Not found\n\n");
				printf("404 lol");
			}
			fflush(stdout);
		}
	}
	return EXIT_FAILURE;
}
