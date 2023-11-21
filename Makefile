FLAGS=-m32 -g2 -fstack-protector-all

all: lamai
obj/runtime.o: runtime/runtime.c
	mkdir -p obj
	$(CC) $(FLAGS) -c runtime/runtime.c -o obj/runtime.o -I runtime
obj/lamai.o: lamai.c
	mkdir -p obj
	$(CC) $(FLAGS) -c lamai.c -o obj/lamai.o
lamai: obj/runtime.o obj/lamai.o
	$(CC) $(FLAGS) obj/runtime.o obj/lamai.o -o lamai