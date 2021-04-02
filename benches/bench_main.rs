use criterion::criterion_main;

mod fibo;

criterion_main!(
    fibo::benches
);
