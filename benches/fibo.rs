// Copyright, 2021, Gé Vissers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use num_traits::{Zero, One};
use babs::{UBigBin8, UBigDec8, UBigBin32, UBigDec32};
use criterion::{Criterion, black_box, criterion_group};

trait Number: One + Zero
    + std::ops::Shl<usize, Output=Self>
    + for <'a> std::ops::Add<&'a Self, Output=Self>
    + for <'a> std::ops::Mul<&'a Self, Output=Self>
    + for <'a> std::ops::Sub<&'a Self, Output=Self> {}

impl Number for UBigBin8 {}
impl Number for UBigDec8 {}
impl Number for UBigBin32 {}
impl Number for UBigDec32 {}

fn fibonacci_work<T>(k: u32) -> (T, T)
where T: Number,
    for <'a> &'a T: std::ops::Shl<usize, Output=T>
{
    let one = T::one();

    if k == 0
    {
        (T::zero(), one)
    }
    else
    {
        let (a, b) = fibonacci_work::<T>(k / 2);
        if k % 2 == 0
        {
            let t = (&b << 1) - &a;
            if k % 4 == 0 { (a*&t, b*&t - &one) } else { (a*&t, b*&t + &one) }
        }
        else
        {
            let t = (&a << 1) + &b;
            if k % 4 == 1 { (a*&t + &one, b*&t) } else { (a*&t - &one, b*&t) }
        }
    }
}

fn fibonacci<T>(k: u32) -> T
where T: Number,
    for <'a> &'a T: std::ops::Shl<usize, Output=T>
{
    match k
    {
        0 => T::zero(),
        1 => T::one(),
        _ => {
            let (a, b) = fibonacci_work::<T>((k-1) / 2);
            if k % 2 == 0
            {
                ((a << 1) + &b) * &b
            }
            else
            {
                let one = T::one();
                let t = ((&b << 1) - &a) * &b;
                if k % 4 == 1 { t - &one } else { t + &one }
            }
        }
    }
}

fn bench_fibonacci(c: &mut Criterion)
{
    c.bench_function("F(100_000), binary, u8", |b| b.iter(|| fibonacci::<UBigBin8>(black_box(100_000))));
    c.bench_function("F(100_000), binary, u32", |b| b.iter(|| fibonacci::<UBigBin32>(black_box(100_000))));
    c.bench_function("F(100_000), decimal, u8", |b| b.iter(|| fibonacci::<UBigDec8>(black_box(100_000))));
    c.bench_function("F(100_000), decimal, u32", |b| b.iter(|| fibonacci::<UBigDec32>(black_box(100_000))));
}

fn bench_fibonacci_4784969(c: &mut Criterion)
{
    let mut group = c.benchmark_group("million-digit-fibonacci");
    // Reduce sample size to keep running time in check
    group.sample_size(10);
    group.bench_function("F(4_784_969), binary, u32", |b| b.iter(|| fibonacci::<UBigBin32>(black_box(4_784_969))));
    group.bench_function("F(4_784_969), decimal, u32", |b| b.iter(|| fibonacci::<UBigDec32>(black_box(4_784_969))));
    group.finish();
}

criterion_group!(benches, bench_fibonacci, bench_fibonacci_4784969);
