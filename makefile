.PHONY: all release build test doc check bench

all: release

release:
	cargo build --release

build:
	cargo build

test:
	cargo test

check:
	cargo check && cargo clippy && cargo fmt --check

doc:
	cargo doc

bench:
	cargo bench -- --output-format=bencher
