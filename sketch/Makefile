ifeq ($(TARGET), cuda)
	EXTRA_FLAGS=-lcuda -lcudart -lnvrtc
	FUTHARK_CMD=cuda
else
	EXTRA_FLAGS=
	FUTHARK_CMD=multicore
endif

run: main
	bash run.sh

main: main.cpp viterbi.o
	g++ -O3 $^ -o $@ $(EXTRA_FLAGS)

viterbi.o: viterbi.c
	gcc -c $< -o $@ $(EXTRA_FLAGS)

viterbi.c: viterbi.fut
	futhark $(FUTHARK_CMD) --library $<

clean:
	rm -f main viterbi.c viterbi.h viterbi.json viterbi.o *.txt
