
OUTC = bin/viterbicall
OUTT = bin/viterbitrain
CC = nvcc
ODIR = tmp
SDIR = src
INC = -I/usr/include/hdf5/serial
LIBS = -lhdf5_serial -lhdf5_cpp -lboost_system -lboost_filesystem -lboost_program_options
CFLAGS = -O3

_OBJC = viterbicall.o viterbi.o model.o signal.o fast5reader.o
OBJC = $(patsubst %,$(ODIR)/%,$(_OBJC))

_OBJT = viterbitrain.o baumwelch.o model.o signal.o
OBJT = $(patsubst %,$(ODIR)/%,$(_OBJT))


all : viterbicall viterbitrain

viterbicall : tmp bin $(OBJC)
	$(CC) -o $(OUTC) $(OBJC) $(LIBS)

viterbitrain : tmp bin $(OBJT)
	$(CC) -o $(OUTT) $(OBJT) $(LIBS)

tmp :
	mkdir tmp

bin :
	mkdir bin

tmp/viterbicall.o : $(SDIR)/viterbicall.cpp
	$(CC) -c $(INC) -o $@ $< $(CFLAGS) 

tmp/viterbitrain.o : $(SDIR)/viterbitrain.cpp
	$(CC) -c $(INC) -o $@ $< $(CFLAGS) 

tmp/viterbi.o : $(SDIR)/viterbi.cu
	$(CC) -c $(INC) -o $@ $< $(CFLAGS) 

tmp/baumwelch.o : $(SDIR)/baumwelch.cu
	$(CC) -c $(INC) -o $@ $< $(CFLAGS) 

tmp/model.o : $(SDIR)/model.cpp
	$(CC) -c $(INC) -o $@ $< $(CFLAGS) 

tmp/signal.o : $(SDIR)/signal.cpp
	$(CC) -c $(INC) -o $@ $< $(CFLAGS) 


tmp/fast5reader.o : $(SDIR)/fast5reader.cpp
	$(CC) -c $(INC) -o $@ $< $(CFLAGS) 

clean :
	rm $(ODIR)/*.o
	rmdir $(ODIR)

