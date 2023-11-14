CPP=g++
FLAGS=-m32 -g2 -fstack-protector-all

all: lamai.o
	$(CPP) $(FLAGS) -o lamai lamai.o runtime/runtime.a

lamai.o: lamai.cpp
	$(CPP) $(FLAGS) -g -c lamai.cpp

clean:
	$(RM) *.a *.o *~ lamai
