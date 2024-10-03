build: wc

clean:
	cargo clean --manifest-path rust/Cargo.toml
	rm -f wc_rust

wc:
	cargo build --bin wc --release --manifest-path rust/Cargo.toml
	mv rust/target/release/wc wc_rust
