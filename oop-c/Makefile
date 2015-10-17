.PHONY: all clean test
all: main
clean:
	rm -f main

CSOURCES=$(wildcard *.c)
CHEADERS=$(wildcard *.h)

main: $(CSOURCES) $(CHEADERS)
	gcc -std=c99 -Wall -Wextra -pedantic -o $@ $(CSOURCES)

test: main
	./$<
