.PHONY: all release build test

all: release

release:
	cargo build --release

build:
	cargo build

test:
	cargo test
