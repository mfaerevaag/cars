MAX_DEPTH ?= 100000

all:

clean:
	rm -f pan*

alley: clean
	spin -a alley/alley.pml
	gcc -DSAFETY -o pan pan.c
	./pan -m$(MAX_DEPTH) -X

barrier: clean
	spin -a barrier/barrier.pml
	gcc -DSAFETY -o pan pan.c
	./pan -m$(MAX_DEPTH) -X

.PHONY: alley barrier
