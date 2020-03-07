use memoise::*;

#[memoise(n <= 100)]
fn fib(n: i64) -> i64 {
    if n == 0 || n == 1 {
        return n;
    }
    fib(n - 1) + fib(n - 2)
}

#[test]
fn fib_test() {
    assert_eq!(267914296, fib(42));
}

#[memoise(-100 <= n <= 100)]
fn foo(n: i64) -> i64 {
    if n == -100 {
        n
    } else {
        foo(n - 1)
    }
}

#[test]
fn foo_test() {
    assert_eq!(foo(100), -100);
}

#[memoise(n <= 100, k <= 50)]
fn comb(n: usize, k: usize) -> usize {
    if k == 0 {
        return 1;
    }
    if n == 0 {
        return 0;
    }
    comb(n - 1, k - 1) + comb(n - 1, k)
}

#[test]
fn comb_test() {
    assert_eq!(1, comb(5, 0));
    assert_eq!(1, comb(5, 5));
    assert_eq!(0, comb(5, 6));
    assert_eq!(10, comb(5, 2));
}

#[test]
fn reset_test() {
    comb_reset();
}

#[memoise(-100 <= n <= 100)]
fn test1(n: i32) -> usize {
    panic!()
}

#[memoise(n + m <= 10000)]
fn test2(n: i32, m: i32) -> usize {
    panic!()
}

#[memoise(n * 100 + m <= 10000)]
fn test3(n: i32, m: i32) -> usize {
    panic!()
}

#[memoise(-10000 <= n * 100 + m <= 10000)]
fn test4(n: i32, m: i32) -> usize {
    panic!()
}

#[memoise_map(n)]
fn fib_map(n: i64) -> i64 {
    if n == 0 || n == 1 {
        return n;
    }
    fib_map(n - 1) + fib_map(n - 2)
}

#[test]
fn fib_map_test() {
    assert_eq!(267914296, fib_map(42));
}

#[memoise_map(n, k)]
fn comb_map(n: usize, k: usize) -> usize {
    if k == 0 {
        return 1;
    }
    if n == 0 {
        return 0;
    }
    comb_map(n - 1, k - 1) + comb_map(n - 1, k)
}

#[test]
fn comb_map_test() {
    assert_eq!(1, comb_map(5, 0));
    assert_eq!(1, comb_map(5, 5));
    comb_map_reset();
    assert_eq!(0, comb_map(5, 6));
    assert_eq!(10, comb_map(5, 2));
}

#[memoise(n < 10)]
fn test_ret_is_not_copy(n: usize) -> String {
    format!("{}", n)
}

#[memoise(n)]
fn fib_no_bounds(n: i64) -> i64 {
    if n == 0 || n == 1 {
        return n;
    }
    fib_no_bounds(n - 1) + fib_no_bounds(n - 2)
}

#[test]
fn fib_no_bounds_test() {
    assert_eq!(267914296, fib_map(42));
}

#[memoise(n, k)]
fn comb_no_bounds(n: usize, k: usize) -> usize {
    if k == 0 {
        return 1;
    }
    if n == 0 {
        return 0;
    }
    comb_no_bounds(n - 1, k - 1) + comb_no_bounds(n - 1, k)
}

#[test]
fn comb_no_bounds_test() {
    assert_eq!(1, comb_no_bounds(5, 0));
    assert_eq!(1, comb_no_bounds(5, 5));
    comb_no_bounds_reset();
    assert_eq!(0, comb_no_bounds(5, 6));
    assert_eq!(10, comb_no_bounds(5, 2));
}
