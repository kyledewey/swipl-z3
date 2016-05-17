build/z3.so: src/z3.c
	mkdir -p build
	swipl-ld -I/home/kyle/stock_z3/with_debug_trace/z3/src/api -L/home/kyle/stock_z3/with_debug_trace/z3/build -g -lz3 -c src/z3.c -o build/z3.o
	swipl-ld -shared -I/home/kyle/stock_z3/with_debug_trace/z3/src/api -L/home/kyle/stock_z3/with_debug_trace/z3/build -g -o build/z3 -lz3 build/z3.o

run: build/z3.so
	LD_LIBRARY_PATH=/home/kyle/stock_z3/with_debug_trace/z3/build swipl -g "load_foreign_library(foreign('/home/kyle/swipl-z3/build/z3.so'))."
