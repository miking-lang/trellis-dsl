main: main.cpp viterbi.o
	g++ -O3 $^

viterbi.o: viterbi.c
	gcc -c $< -o $@

viterbi.c: viterbi.fut
	futhark multicore --library $<
