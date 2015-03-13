#define _POSIX_C_SOURCE 1

#include <stdint.h>

void reverse (char* begin, char* end)
{
	--end;
	while (begin < end) {
		char tmp = *begin;
		*begin = *end;
		*end = tmp;
		++begin;
		--end;
	}
}

char* format_uint16 (char buffer [static 6], uint16_t value)
{
	char* cursor = buffer;
	do {
		*cursor = "0123456789" [value % 10];
		value /= 10;
		++cursor;
	} while (value != 0);

	reverse (buffer, cursor);
	return cursor;
}

char* format_int16 (char buffer [static 7], int16_t value)
{
	if (value < 0) {
		buffer [0] = '-';
		return format_uint16 (buffer + 1, -(int32_t)value);
	}
	else
		return format_uint16 (buffer, value);
}


#include <signal.h>
#include <unistd.h>
#include <stdlib.h>
#include <errno.h>
#include <stdio.h>

void handler (int sig)
{
	char buffer [] = "Caught signal SXXXXX";
	char* end = format_int16 (buffer + 14, sig);
	*end++ = '\n';
	write (STDOUT_FILENO, buffer, end - buffer);
}

int main (void)
{
	struct sigaction action = {
		.sa_handler = &handler,
		.sa_mask    = 0,
		.sa_flags   = 0
	};

	int signals [] = {
		SIGHUP,  SIGINT,  SIGQUIT, SIGILL,
		SIGABRT, SIGFPE,  SIGKILL, SIGSEGV,
		SIGPIPE, SIGALRM, SIGTERM, SIGUSR1,
		SIGUSR2, SIGCHLD, SIGCONT, SIGSTOP,
		SIGTSTP, SIGTTIN, SIGTTOU,

		SIGBUS,  SIGPOLL, SIGPROF,   SIGSYS,
		SIGTRAP, SIGURG,  SIGVTALRM, SIGXCPU,
		SIGXFSZ
	};

	for (int i = 0; i < sizeof (signals) / sizeof (*signals); ++i)
		sigaction (signals [i], &action, NULL);

	while (1) {
		char unused [256];
		ssize_t ret = read (STDIN_FILENO, unused, 256);
		switch (ret) {
			case -1:
				switch (errno) {
					case EAGAIN:
						break;
					case EINTR:
						break;
					default:
						perror (NULL);
						return EXIT_FAILURE;
				}
				break;
			case 0:
				return EXIT_SUCCESS;
			default:
				break;
		}
	}
}
