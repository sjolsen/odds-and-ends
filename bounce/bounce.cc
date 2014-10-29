//
// This file is Copyright (C) 2014 by Jesper Juhl <jj@chaosbits.net>
// This file may be freely used under the terms of the zlib license (http://opensource.org/licenses/Zlib)
//
// This software is provided 'as-is', without any express or implied warranty.
// In no event will the authors be held liable for any damages arising from the use of this software.
//
// Permission is granted to anyone to use this software for any purpose,
// including commercial applications, and to alter it and redistribute it freely,
// subject to the following restrictions:
//
//    1. The origin of this software must not be misrepresented; you must not claim that you wrote
//       the original software. If you use this software in a product, an acknowledgment in the
//       product documentation would be appreciated but is not required.
//
//    2. Altered source versions must be plainly marked as such, and must not be misrepresented as
//       being the original software.
//
//    3. This notice may not be removed or altered from any source distribution.

// This is an altered source version. It is not the original software.

#include <SFML/Graphics.hpp>
#include <random>
#include <functional>
#include <cstdlib>
#include <cmath>

class Ball
{
	sf::CircleShape _circle;
	sf::Vector2f _velocity;

	friend decltype (auto) draw (sf::RenderWindow& window, const Ball& Ball);

public:
	Ball (sf::Vector2f initial_position,
	      sf::Vector2f initial_velocity,
	      sf::Color color,
	      float radius,
	      float border)
		: _circle (radius - border),
		  _velocity (initial_velocity)
	{
		_circle.setOutlineThickness (border);
		_circle.setOutlineColor (sf::Color::Black);
		_circle.setFillColor (color);
		_circle.setOrigin (radius - border, radius - border);
		_circle.setPosition (initial_position);
	}

	Ball () = default;
	Ball (const Ball&) = delete;
	Ball (Ball&&) = default;
	Ball& operator = (Ball&&) = default;
	~Ball () = default;

	auto radius () const
	{
		return _circle.getRadius () + _circle.getOutlineThickness ();
	}

	sf::Vector2f position () const
	{
		return _circle.getPosition ();
	}

	sf::Vector2f velocity () const
	{
		return _velocity;
	}

	void set_position (sf::Vector2f position)
	{
		_circle.setPosition (position);
	}

	void set_velocity (sf::Vector2f velocity)
	{
		_velocity = velocity;
	}
};

decltype (auto) draw (sf::RenderWindow& window, const Ball& Ball)
{
	return window.draw (Ball._circle);
}



void collide (Ball& ball, sf::Time interval, unsigned int window_width, unsigned int window_height)
{
	const auto delta = interval.asSeconds () * ball.velocity ();
	auto pos = ball.position () + delta;

	if (pos.x - ball.radius () < 0) { // left window edge
		ball.set_velocity ({ball.velocity ().x * -1, ball.velocity ().y});
		pos.x = 0 + ball.radius ();
	} else if (pos.x + ball.radius () >= window_width) { // right window edge
		ball.set_velocity ({ball.velocity ().x * -1, ball.velocity ().y});
		pos.x = window_width - ball.radius ();
	}
	if (pos.y - ball.radius () < 0) { // top of window
		ball.set_velocity ({ball.velocity ().x, ball.velocity ().y * -1});
		pos.y = 0 + ball.radius ();
	} else if (pos.y + ball.radius () >= window_height) { // bottom of window
		ball.set_velocity ({ball.velocity ().x, ball.velocity ().y * -1});
		pos.y = window_height - ball.radius ();
	}

	ball.set_position (pos);
}

static inline
float dot (sf::Vector2f x, sf::Vector2f y)
{
	return x.x * y.x + x.y * y.y;
}

static inline
float magnitude_sq (sf::Vector2f x)
{
	return dot (x, x);
}

static inline
sf::Vector2f direction (sf::Vector2f v)
{
	return v / std::sqrt (magnitude_sq (v));
}

static inline
float distance (sf::Vector2f x, sf::Vector2f y)
{
	return std::sqrt (magnitude_sq (y - x));
}

static inline
sf::Vector2f proj (sf::Vector2f a, sf::Vector2f b)
// Projection of a onto b
{
	return (dot (a, b) / magnitude_sq (b)) * b;
}

static inline
float backup (Ball& b1, Ball& b2)
{
	const auto v1 = b1.velocity ();
	const auto v2 = b2.velocity ();
	const auto x1 = b1.position ();
	const auto x2 = b2.position ();
	const auto r1 = b1.radius ();
	const auto r2 = b1.radius ();

	const auto t = (r1 + r2 - distance (x1, x2)) / distance (v1, v2);
	b1.set_position (x1 - v1 * t);
	b2.set_position (x2 - v2 * t);
	return t;
}

void collide (Ball& b1, Ball& b2)
{
	if (distance (b1.position (), b2.position ()) > (b1.radius () + b2.radius ()))
		return;

	const auto t = backup (b1, b2);

	const auto x1 = b1.position ();
	const auto x2 = b2.position ();
	const auto r1 = b1.radius ();
	const auto r2 = b1.radius ();
	const auto d = x2 - x1;
	const auto v1 = b1.velocity ();
	const auto v2 = b2.velocity ();
	const auto v1p = v1 - proj (v1 - v2, -d);
	const auto v2p = v2 - proj (v2 - v1, d);

	b1.set_velocity (v1p);
	b2.set_velocity (v2p);
	b1.set_position (x1 + v1p * t);
	b2.set_position (x2 + v2p * t);
}

void accelerate (Ball& ball, sf::Time interval, sf::Vector2f acceleration)
{
	ball.set_velocity (ball.velocity () + acceleration * interval.asSeconds ());
}

void drag (Ball& ball, sf::Time interval, float factor)
{
	const auto v = ball.velocity ();
	const auto f = factor * magnitude_sq (v);
	accelerate (ball, interval, f * -direction (v));
}



template <typename ThetaGen>
sf::Vector2f random_direction (ThetaGen&& theta_gen)
{
	auto theta = theta_gen ();
	return {std::cos (theta), std::sin (theta)};
}

template <typename URNG>
Ball random_ball (URNG&& gen, float speed, float radius, unsigned int window_width, unsigned int window_height)
{
	static const sf::Color colors [] = {
		sf::Color::Black,
		sf::Color::White,
		sf::Color::Red,
		sf::Color::Green,
		sf::Color::Blue,
		sf::Color::Yellow,
		sf::Color::Magenta,
		sf::Color::Cyan
	};

	std::uniform_real_distribution <float> posx (0, window_width);
	std::uniform_real_distribution <float> posy (0, window_height);
	std::uniform_real_distribution <float> theta (0, 2 * M_PI);
	std::uniform_int_distribution <int> color (0, std::end (colors) - std::begin (colors) - 1);

	return Ball ({posx (gen), posy (gen)},
	             speed * random_direction ([&] { return theta (gen); }),
	             colors [color (gen)],
	             radius,
	             2);
}

void do_physics (Ball* begin, Ball* end, sf::Time update_ms, float dragf, sf::Vector2f acceleration, unsigned int window_width, unsigned int window_height)
{
	for (auto b1 = begin; b1 != end; ++b1)
		for (auto b2 = b1 + 1; b2 != end; ++b2)
			collide (*b1, *b2);

	for (auto b1 = begin; b1 != end; ++b1)
	{
		collide (*b1, update_ms, window_width, window_height);
		drag (*b1, update_ms, dragf);
		accelerate (*b1, update_ms, acceleration);
	}
}

int main()
{
	unsigned int window_width = 800;
	unsigned int window_height = 600;
	const int bpp = 32;
	const float speed = 300;
	const sf::Vector2f acceleration = {0.0f, 000.0f};
	const float dragf = 0.000f;

	sf::View view ({window_width/2.0f, window_height/2.0f}, {(float)window_width, (float)window_height});
	sf::RenderWindow window(sf::VideoMode(window_width, window_height, bpp), "Bouncing ball");
	window.setView (view);
	window.setVerticalSyncEnabled(true);

	std::random_device seed_device;
	std::default_random_engine engine(seed_device());

	Ball balls [400];
	for (Ball& b : balls)
		b = random_ball (engine, speed, 8, window_width/8, window_height/8);

	sf::Clock clock;
	sf::Time elapsed = clock.restart();
	const sf::Time update_ms = sf::seconds(1.f / 120.f);
	while (window.isOpen()) {
		sf::Event event;
		while (window.pollEvent(event)) {
			if ((event.type == sf::Event::Closed) ||
			    ((event.type == sf::Event::KeyPressed) && (event.key.code == sf::Keyboard::Escape))) {
				window.close();
				break;
			}
			if (event.type == sf::Event::Resized) {
				window_width = event.size.width;
				window_height = event.size.height;
				view.reset ({0.0f, 0.0f, (float)window_width, (float)window_height});
				window.setView (view);
				break;
			}
		}

		elapsed += clock.restart();
		while (elapsed >= update_ms) {
			do_physics (std::begin (balls), std::end (balls), update_ms, dragf, acceleration, window_width, window_height);
			elapsed -= update_ms;
		}

		window.clear(sf::Color(58, 110, 165));
		for (const Ball& b : balls)
			draw (window, b);
		window.display();
	}

	return EXIT_SUCCESS;
}
