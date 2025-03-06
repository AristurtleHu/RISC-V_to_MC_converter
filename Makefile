CC = gcc
CFLAGS = -g -std=c11 -Wpedantic -Wall -Wextra -Werror
ASSEMBLER_FILES = src/tables.c src/utils.c src/translate_utils.c src/translate.c src/block.c
NEW_TEST ?= Single

all: assembler

.PHONY: assembler clean check grade

assembler: clean
	$(CC) $(CFLAGS) -o assembler assembler.c $(ASSEMBLER_FILES)

clean:
	-$(MAKE) -C test clean
	-rm -f *.o assembler
	-rm -rf out
	-rm -rf __pycache__

check: assembler
	$(MAKE) -C test check

test: assembler
	$(MAKE) -C test test TEST_NAME=$(TEST_NAME) 

TEST_NAME ?= "labels"