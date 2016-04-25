build/z3.o: src/z3.c
	swipl-ld -I/home/kyle/stock_z3/with_debug_trace/z3/src/api -L/home/kyle/stock_z3/with_debug_trace/z3/build -lz3 -c src/z3.c -o build/z3.o
	swipl-ld -shared -I/home/kyle/stock_z3/with_debug_trace/z3/src/api -L/home/kyle/stock_z3/with_debug_trace/z3/build -o build/z3 -lz3 build/z3.o

run: build/z3.o
	swipl -g "load_foreign_library(foreign('/home/kyle/swipl-z3/build/z3.so'))."
