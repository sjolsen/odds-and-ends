#ifndef RINGBUFFER_HH
#define RINGBUFFER_HH

// #include <algorithm>
#include <unistd.h>

#define RWERROR (static_cast <std::size_t> (-1))

// Return RWERROR on failure or EOF, the number of bytes read otherwise
static inline
std::size_t xread (int fd, char* dst, std::size_t len)
{
	int n = ::read (fd, static_cast <void*> (dst), len);
	switch (n)
	{
	case -1:
		if (errno == EAGAIN || errno == EINTR)
			return 0;
		else
			return RWERROR;
	case 0:
		if (len == 0)
			return 0;
		else
			return RWERROR;
	default:
		return n;
	}
}

// Return RWERROR on failure, the number of bytes written otherwise
static inline
std::size_t xwrite (int fd, const char* src, std::size_t len)
{
	int n = ::write (fd, static_cast <const void*> (src), len);
	switch (n)
	{
	case -1:
		if (errno == EAGAIN || errno == EINTR)
			return 0;
		else
			return RWERROR;
	case 0:
		if (len == 0)
			return 0;
		else
			return RWERROR;
	default:
		return n;
	}
}

class ringbuffer
{
	char* const buffer;
	const std::size_t length;
	std::size_t wcursor = 0;
	std::size_t rcursor = 0;

public:
	std::size_t fill () const
	{
		if (wcursor < rcursor)
			return (wcursor + length) - rcursor;
		else
			return wcursor - rcursor;
	}

	std::size_t capacity () const
	{
		return length - 1;
	}

public:
	ringbuffer (char* buffer, std::size_t length)
		: buffer {buffer},
		  length {length}
	{
	}

	template <std::size_t N>
	ringbuffer (char (&buffer) [N])
		: ringbuffer (buffer, N)
	{
	}

	bool empty () const
	{
		return fill () == 0;
	}

	bool full () const
	{
		return fill () == capacity ();
	}

	// std::size_t write (const char* data, std::size_t n)
	// {
	// 	n = std::min (n, capacity () - fill ());
	// 	auto n1 = std::min (n, length - wcursor);
	// 	auto n2 = n - n1;

	// 	std::copy_n (data, n1, buffer + wcursor);
	// 	wcursor = (wcursor + n1) % length;

	// 	std::copy_n (data + n1, n2, buffer + wcursor);
	// 	wcursor += n2;

	// 	return n;
	// }

	// std::size_t read (char* data, std::size_t n)
	// {
	// 	n = std::min (n, fill ());
	// 	auto n1 = std::min (n, length - rcursor);
	// 	auto n2 = n - n1;

	// 	std::copy_n (buffer + rcursor, n1, data);
	// 	rcursor = (rcursor + n1) % length;

	// 	std::copy_n (buffer + rcursor, n2, data + n1);
	// 	rcursor += n2;

	// 	return n;
	// }

	std::size_t read (int fd)
	{
		auto n  = capacity () - fill ();
		auto n1 = std::min (n, length - wcursor);
		auto n2 = n - n1;

		auto nread1 = xread (fd, buffer + wcursor, n1);
		if (nread1 == RWERROR)
			return RWERROR;
		wcursor = (wcursor + nread1) % length;
		if (nread1 < n1)
			return nread1;

		auto nread2 = xread (fd, buffer + wcursor, n2);
		if (nread2 == RWERROR)
			return RWERROR;
		wcursor = (wcursor + nread2) % length;

		return nread1 + nread2;
	}

	std::size_t write (int fd)
	{
		auto n  = fill ();
		auto n1 = std::min (n, length - rcursor);
		auto n2 = n - n1;

		auto nwritten1 = xwrite (fd, buffer + rcursor, n1);
		if (nwritten1 == RWERROR)
			return RWERROR;
		rcursor = (rcursor + nwritten1) % length;
		if (nwritten1 < n1)
			return nwritten1;

		auto nwritten2 = xwrite (fd, buffer + rcursor, n2);
		if (nwritten2 == RWERROR)
			return RWERROR;
		rcursor = (rcursor + nwritten2) % length;

		return nwritten1 + nwritten2;
	}
};

#endif
