z3.o: z3.c
	swipl-ld -I/home/kyle/stock_z3/with_debug_trace/z3/src/api -L/home/kyle/stock_z3/with_debug_trace/z3/build -lz3 -c z3.c
	swipl-ld -shared -I/home/kyle/stock_z3/with_debug_trace/z3/src/api -L/home/kyle/stock_z3/with_debug_trace/z3/build -o z3 -lz3 z3.o

run: z3.o
	swipl -g "load_foreign_library(foreign('/home/kyle/swipl-z3/src/z3.so'))."
