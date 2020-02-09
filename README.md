# memoise [![crate-name at crates.io](https://img.shields.io/crates/v/memoise.svg)](https://crates.io/crates/memoise) [![crate-name at docs.rs](https://docs.rs/memoise/badge.svg)](https://docs.rs/memoise)

Simple memoization library for rust

# Documentation

Find it on [docs.rs](https://docs.rs/memoise).

# Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
memoise = "0.2"
```

And then, just add `memoise` attribute to functions you want to memoise:

```rs
use memoise::memoise;

#[memoise(n <= 100)]
fn fib(n: i64) -> i64 {
    if n == 0 || n == 1 {
        return n;
    }
    fib(n - 1) + fib(n - 2)
}
```

And you can call it normally:

```rs
fn main() {
    println!("{}", fib(45));
}
```

And run it:

```sh
$ cargo build --release
$ time cargo run --release -q
1134903170

real    0m0.039s
user    0m0.000s
sys     0m0.016s
```

If comment out `memoise` attribute, it will not be memoised.

```rs
// #[memoise(n <= 100)]
fn fib(n: i64) -> i64 {
    if n == 0 || n == 1 {
        return n;
    }
    fib(n - 1) + fib(n - 2)
}
```

```sh
$ cargo build --release
$ time cargo run --release -q
1134903170

real    0m5.019s
user    0m4.984s
sys     0m0.016s
```

For more information, you can find a document on [docs.rs](https://docs.rs/memoise).
