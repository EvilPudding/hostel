all:
	cc -std=c89 -pedantic -Wall -Ofast main.c -o hostel

install: all
	sudo cp hostel /usr/bin/hostel

uninstall:
	sudo rm /usr/bin/hostel
