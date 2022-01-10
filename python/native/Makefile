all:
	gcc -fPIC -shared wrapperForPython.c -o libfuzzy_python.so -L. -lZ3Fuzzy -L../fuzzysat/z3 -lz3

clean:
	rm libfuzzy_python.so
