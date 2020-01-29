extern crate memoise;

use memoise::memoise;

#[memoise(keys(n = 100))]
fn fib(n: usize) -> usize {
    if n == 0 || n == 1 {
        return n;
    }
    fib(n - 1) + fib(n - 2)
}

#[test]
fn test_fib() {
    assert_eq!(267914296, fib(42));
}

#[memoise(keys(n = 100, m = 50))]
fn comb(n: usize, m: usize) -> usize {
    if m == 0 {
        return 1;
    }
    if n == 0 {
        return 0;
    }
    comb(n - 1, m - 1) + comb(n - 1, m)
}

#[test]
fn comb_test() {
    assert_eq!(1, comb(5, 0));
    assert_eq!(1, comb(5, 5));
    assert_eq!(0, comb(5, 6));
    assert_eq!(10, comb(5, 2));
}
