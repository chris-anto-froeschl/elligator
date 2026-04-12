.PHONY: lint lint-style all

all: build lint lint-style

build:
	lake build

lint:
	lake lint

lint-style:
	lake exe lint-style


