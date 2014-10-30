#ifndef VECTORS_HH
#define VECTORS_HH

#include <SFML/Graphics.hpp>
#include <cmath>

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

#endif
