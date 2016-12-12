all: fire

fire: fire.cpp
	g++ -g fire.cpp -Wall -o fire -lX11 -lm -lXext

clean:
	rm -f fire
	rm -f *.o

