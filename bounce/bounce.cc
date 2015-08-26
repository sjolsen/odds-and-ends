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
#include "vectors.hh"

class Ball
{
	sf::CircleShape _circle;
	sf::Vector2f _velocity;

	friend void draw (sf::RenderWindow& window, const Ball& Ball);

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

	auto color () const
	{
		return _circle.getFillColor ();
	}

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

void draw (sf::RenderWindow& window, const Ball& Ball)
{
	window.draw (Ball._circle);
}



struct bounding_box
{
	float left;
	float top;
	float right;
	float bottom;
};

static inline
float backup (Ball& ball, bounding_box box)
{
	const auto r = ball.radius ();
	auto x = ball.position ();
	auto v = ball.velocity ();

	const auto left = box.left + r;
	const auto right = box.right - r;
	const auto top = box.top + r;
	const auto bottom = box.bottom - r;

	float t = 0.0f;
	auto nv = -v;
	if (x.x < left)
		t = std::max (t, std::abs ((x.x - left) / v.x));
	else if (x.x > right)
		t = std::max (t, std::abs ((x.x - right) / v.x));
	else
		nv.x = v.x;
	if (x.y < top)
		t = std::max (t, std::abs ((x.y - top) / v.y));
	else if (x.y > bottom)
		t = std::max (t, std::abs ((x.y - bottom) / v.y));
	else
		nv.y = v.y;

	ball.set_position (x - v * t);
	ball.set_velocity (nv);
	return t;
}

void collide (Ball& b, bounding_box box)
{
	float t = 0.0f;
	while ((t = backup (b, box)) != 0.0f)
		b.set_position (b.position () + b.velocity () * t);
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

void attract (Ball& b1, Ball& b2, sf::Time interval, float factor)
{
	const auto x1 = b1.position ();
	const auto x2 = b2.position ();
	const auto d = distance (x1, x2);
	const auto f = factor / (d * d);

	if (b1.color () == b2.color ())
	{
		accelerate (b1, interval, f * direction (x2 - x1));
		accelerate (b2, interval, f * direction (x1 - x2));
	}
	else
	{
		accelerate (b1, interval, f * -direction (x2 - x1));
		accelerate (b2, interval, f * -direction (x1 - x2));
	}
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

	std::uniform_real_distribution <float> posx (radius, window_width - radius);
	std::uniform_real_distribution <float> posy (radius, window_height - radius);
	std::uniform_real_distribution <float> theta (0, 2 * M_PI);
	std::uniform_int_distribution <int> color (0, std::end (colors) - std::begin (colors) - 1);

	return Ball ({posx (gen), posy (gen)},
	             speed * random_direction ([&] { return theta (gen); }),
	             colors [color (gen)],
	             radius,
	             0);
}

void do_physics (Ball* begin, Ball* end, sf::Time update_ms, float dragf, float attractf, sf::Vector2f acceleration, unsigned int window_width, unsigned int window_height)
{
	for (auto b1 = begin; b1 != end; ++b1)
		b1->set_position (b1->position () + b1->velocity () * update_ms.asSeconds ());

	for (auto b1 = begin; b1 != end; ++b1)
		for (auto b2 = b1 + 1; b2 != end; ++b2)
		{
			collide (*b1, *b2);
			attract (*b1, *b2, update_ms, attractf);
		}

	for (auto b1 = begin; b1 != end; ++b1)
	{
		collide (*b1, bounding_box {0.0f, 0.0f, (float)window_width, (float)window_height});
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
	const sf::Vector2f acceleration = {0.0f, 00.0f};
	const float dragf = 0.00f;
	const float attractf = 00000.0f;

//	sf::View view ({0.0f, 0.0f, (float)window_width, (float)window_height});
	sf::RenderWindow window(sf::VideoMode(window_width, window_height, bpp), "Bouncing ball");
//	window.setView (view);
	window.setVerticalSyncEnabled(true);
//	auto wpos = window.getPosition ();

	std::random_device seed_device;
	std::default_random_engine engine(seed_device());

	Ball balls [100];
	for (Ball& b : balls)
		b = random_ball (engine, speed, 8, window_width, window_height);

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
			// if (event.type == sf::Event::Resized) {
			// 	window_width = event.size.width;
			// 	window_height = event.size.height;
			// 	view.reset ({0.0f, 0.0f, (float)window_width, (float)window_height});
			// 	view.setViewport ({0.0f, 0.0f, 1.0f, 1.0f});
			// 	window.setView (view);
			// 	break;
			// }
		}

		// auto nwpos = window.getPosition ();
		// for (Ball& b : balls)
		// 	b.set_position ({b.position ().x + (wpos - nwpos).x,
		// 	                 b.position ().y + (wpos - nwpos).y});
		// wpos = nwpos;

		elapsed += clock.restart();
		while (elapsed >= update_ms) {
			do_physics (std::begin (balls), std::end (balls), update_ms, dragf, attractf, acceleration, window_width, window_height);
			elapsed -= update_ms;
		}

		window.clear(sf::Color(58, 110, 165));
		for (const Ball& b : balls)
			draw (window, b);
		window.display();
	}

	return EXIT_SUCCESS;
}
