.PHONY: all release build test bench

all: release

release:
	cargo build --release

build:
	cargo build

test:
	cargo test

bench:
	cargo bench -- --output-format=bencher
