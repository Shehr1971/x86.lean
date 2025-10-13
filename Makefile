out: helpers.o out.o
	$(CC) $^ -o $@

out.s: out.src
	cat out.src | lake exec compiler > $@
