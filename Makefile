.PHONY: lint lint-style all

all: build lint lint-style

build:
	LEAN_NUM_THREADS=64 lake build

lint:
	LEAN_NUM_THREADS=64 lake lint

lint-style:
	lake exe lint-style


