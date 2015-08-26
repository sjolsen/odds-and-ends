.PHONY: all test clean
all: bounce

test: bounce
	./bounce

clean:
	rm ./bounce

bounce: bounce.cc vectors.hh
	g++ -std=c++14 $< -o $@ -lsfml-graphics -lsfml-window -lsfml-system
