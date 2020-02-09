#[memoise::memoise(n <= 100)]
fn fib(n: i64) -> i64 {
    if n == 0 || n == 1 {
        return n;
    }
    fib(n - 1) + fib(n - 2)
}

fn main() {
    println!("{}", fib(45));
}
