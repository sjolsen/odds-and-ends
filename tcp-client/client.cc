#include <iostream>
#include <cstdlib>
#include <stdexcept>
#include <limits>
#include <cstring>
#include <thread>

#include "ringbuffer.hh"

#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>

std::ostream& print (std::ostream& os)
{
	return os;
}

template <typename First, typename... Rest>
std::ostream& print (std::ostream& os, First&& first, Rest&&... rest)
{
	return print (os << std::forward <First> (first), std::forward <Rest> (rest)...);
}

template <typename Int>
Int string_to (const std::string& s)
{
	auto n = std::stoll (std::string {s});
	if (n > std::numeric_limits <Int>::max ())
		throw std::out_of_range ("string_to");
	return n;
}



template <typename... Args>
[[noreturn]]
void error (Args&&... args)
{
	print (std::cerr, std::forward <Args> (args)...);
	std::cerr << std::endl;
	std::exit (EXIT_FAILURE);
}

void fd_splice (int input, int output)
{
	char buffer_store [1024];
	ringbuffer buffer (buffer_store);

	while (true)
	{
		if (!buffer.empty ())
			if (buffer.write (output) == RWERROR)
				break;
		if (!buffer.full ())
			if (buffer.read (input) == RWERROR)
				break;
	}

	while (!buffer.empty ())
		if (buffer.write (output) == RWERROR)
			break;
}

int main (int argc, const char* const* argv)
{
	if (argc < 3)
		error ("Usage: ", argv [0], " hostname port");
	auto hosts = argv [1];
	auto ports = argv [2];

	auto port = [&] {
		try {
			return string_to <std::uint16_t> (ports);
		}
		catch (std::exception&) {
			error ("Invalid port: ", ports);
		}
	} ();

	auto sockfd = ::socket (AF_INET, SOCK_STREAM, 0);
	if (sockfd < 0)
		error ("Error opening socket");

	auto server = gethostbyname (hosts);
	if (!server)
		error ("Invalid hostname:", hosts);

	in_addr server_address;
	memcpy (&server_address.s_addr, server->h_addr, sizeof (server_address.s_addr));

	sockaddr_in serv_addr = {
		/* .sin_family = */ AF_INET,
		/* .sin_port   = */ ::htons (port),
		/* .sin_addr   = */ server_address,
		/* .sin_zero   = */ {}
	};

	if (::connect (sockfd, reinterpret_cast <sockaddr*> (&serv_addr), sizeof (serv_addr)) < 0)
		error ("Error connecting to ", hosts, ":", ports);

	auto receive = std::thread (fd_splice, sockfd, STDOUT_FILENO);
	fd_splice (STDIN_FILENO, sockfd);
	::shutdown (sockfd, SHUT_WR);
	receive.join ();
	::close (sockfd);

	return EXIT_SUCCESS;
}
