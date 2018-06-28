pan.c: reliable.pml reliable.nvc
	spin -a -F reliable.nvc reliable.pml

pan: pan.c
	gcc -march=native -O3 -o $@ $< -DCOLLAPSE

build: pan


# pand options:
# -a find acceptance cycles
# -f add weak fairness (to -a or -l)
run: build
	./pan -a -f


clean:
	rm --verbose pan.* *.trail


.PHONY := clean run
