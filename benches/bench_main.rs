use criterion::criterion_main;

mod base;
mod divbase;
mod fibo;

criterion_main!(
    base::benches,
    divbase::benches,
    fibo::benches
);
