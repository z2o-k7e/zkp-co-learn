# Halo2 Examples

This repo includes a few simple examples to illustrate how to write circuit in Halo2.

## Instruction

Compile the repo

```
cargo build
```

Run examples
```
cargo test -- --nocapture test_example1
cargo test -- --nocapture test_example2
cargo test -- --nocapture test_example3
```

Plot the circuit layout
```
cargo test --all-features -- --nocapture plot
cargo test --all-features -- --nocapture print

cargo test --all-features -- --nocapture plot_fibo1
cargo test --all-features -- --nocapture plot_fibo2
cargo test --all-features -- --nocapture plot_fibo3

cargo test --release --all-features print_range_check_1
cargo test --release --all-features print_range_check_2
cargo test --release --all-features print_range_check_3

# decompose
cargo test --release --all-features print_decompose_range_check_1
```


# halo2-learn
