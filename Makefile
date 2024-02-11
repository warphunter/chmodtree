CC = gcc # - need GCC2.5 or higher
CFLAGS = -pipe -O2 -funroll-loops -Wall -Winline -D_LARGEFILE_SOURCE -D_FILE_OFFSET_BITS=64
OLDTIMERCFLAGS = --param inline-unit-growth=100 --param large-function-growth=110000 # - for gcc 3.4.3, 3.4.6
BESTCFLAGSONLINUX = -pipe -O3 -march=native -funroll-loops -Wall -Winline -D_LARGEFILE_SOURCE -D_FILE_OFFSET_BITS=64
CFLAGSWIN = -pipe -O2 -Wall -Winline -Wno-int-to-pointer-cast -Wno-pointer-to-int-cast -I. -D_POSIX_C_SOURCE
LIBS = -lpthread -lrt
ALTLIBS = -lpthread

SRC = chmodtree.c
INC = commonlib.h
BIN = $(SRC:.c=)
DEP = setmode.c
MAN = chmodtree.1

all: $(BIN)

$(BIN): $(SRC) $(INC) $(DEP)
	@export PATH; PATH=${PATH}:/usr/local/bin:/opt/freeware/bin; \
	case `uname -s` in \
	    SunOS) \
		set -x; \
		$(CC) -DCC_USED="\"`gcc --version|awk '/gcc/ {print $$0 \", flags:\"}'` $(CFLAGS) -pthreads -m64 $(OLDTIMERCFLAGS) -D_POSIX_PTHREAD_SEMANTICS\"" $(CFLAGS) -pthreads -m64 $(OLDTIMERCFLAGS) -D_POSIX_PTHREAD_SEMANTICS $(SRC) $(DEP) -o $@ $(LIBS) \
		;; \
	    AIX) \
		set -x; \
		$(CC) -DCC_USED="\"`gcc --version|awk '/gcc/ {sub(\")\",\"\",$$NF); print \"gcc version \" $$NF \", flags:\"}'` $(CFLAGS) -pthread -maix64 -D_LARGE_FILES\"" $(CFLAGS) -pthread -maix64 -D_LARGE_FILES $(SRC) $(DEP) -o $@ $(LIBS) \
		;; \
	    HP-UX) \
		case `uname -m` in \
		    ia64) \
			set -x; \
			$(CC) -DCC_USED="\"`gcc --version|awk '/gcc/ {sub(\")\",\"\",$$NF); print \"gcc version \" $$NF \", flags:\"}'` $(CFLAGS) -pthread -mlp64 -D_INCLUDE_POSIX_SOURCE -D_XOPEN_SOURCE_EXTENDED\"" $(CFLAGS) -pthread -mlp64 -D_INCLUDE_POSIX_SOURCE -D_XOPEN_SOURCE_EXTENDED $(SRC) $(DEP) -o $@ $(LIBS) \
			;; \
		    9000/800) \
			set -x; \
			$(CC) -DCC_USED="\"`gcc --version|awk '/gcc/ {sub(\")\",\"\",$$NF); print \"gcc version \" $$NF \", flags:\"}'` $(CFLAGS) -pthread -munix=98 -D_INCLUDE_POSIX_SOURCE -D_XOPEN_SOURCE_EXTENDED\"" $(CFLAGS) -pthread -munix=98 -D_INCLUDE_POSIX_SOURCE -D_XOPEN_SOURCE_EXTENDED $(SRC) $(DEP) -o $@ $(LIBS); \
		esac \
		;; \
	    Linux) \
		set -x; \
		$(CC) -DCC_USED="\"`gcc --version|awk '/gcc/ {print $$0 \", flags:\"}'` -mcpu=native $(CFLAGS) $(OLDTIMERCFLAGS) -pthread\"" -march=native $(CFLAGS) $(OLDTIMERCFLAGS) -pthread $(SRC) $(DEP) -o $@ $(LIBS) \
		;; \
	    FreeBSD) \
		set -x; \
		$(CC) -DCC_USED="\"`gcc --version|awk '/gcc/ {print $$0 \", flags:\"}'` $(CFLAGS) $(OLDTIMERCFLAGS) -pthread -march=native\"" $(CFLAGS) -march=native $(SRC) $(DEP) -o $@ $(LIBS) \
		;; \
	    OpenBSD|Darwin) \
		set -x; \
		$(CC) -DCC_USED="\"`gcc --version|awk '/gcc/ {sub(\")\",\"\",$$NF); print \"gcc version \" $$NF \", flags:\"}'` $(CFLAGS) $(OLDTIMERCFLAGS) -pthread -march=native\"" $(CFLAGS) -march=native $(SRC) $(DEP) -o $@ $(ALTLIBS) \
		;; \
	    *) \
		echo `uname -s` has not been tested.; \
		echo You might try: gcc -pthread -O2 $(SRC) $(DEP) -o $(BIN) -lpthread -lrt \
		;; \
	esac

install: $(BIN)
	mkdir -p /usr/local/bin && cp -p $(BIN) /usr/local/bin; \
	test -d /usr/local/share/man/man1 && cp -p $(MAN) /usr/local/share/man/man1; \
	exit 0

uninstall:
	rm -f /usr/local/bin/$(BIN); \
	test -f /usr/local/share/man/man1/$(MAN) && rm -f /usr/local/share/man/man1/$(MAN); \
	exit 0

clean:
	-rm -f $(BIN)

.PHONY : all install uninstall clean
