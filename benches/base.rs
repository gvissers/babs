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

use num_traits::One;
use babs::{UBigBin8, UBigBin32, UBigBin64};
use criterion::{Criterion, black_box, criterion_group};

fn bench_to_decimal(c: &mut Criterion)
{
    let n = UBigBin8::one() << 100_000;
    c.bench_function("to_decimal 2^100_000), u8", |b| b.iter(|| black_box(&n).to_decimal()));
    let n = UBigBin32::one() << 100_000;
    c.bench_function("to_decimal 2^100_000), u32", |b| b.iter(|| black_box(&n).to_decimal()));
    let n = UBigBin64::one() << 100_000;
    c.bench_function("to_decimal 2^100_000), u64", |b| b.iter(|| black_box(&n).to_decimal()));
    let n = UBigBin8::one() << 1_000_000;
    c.bench_function("to_decimal 2^1_000_000), u8", |b| b.iter(|| black_box(&n).to_decimal()));
    let n = UBigBin32::one() << 1_000_000;
    c.bench_function("to_decimal 2^1_000_000), u32", |b| b.iter(|| black_box(&n).to_decimal()));
    let n = UBigBin64::one() << 1_000_000;
    c.bench_function("to_decimal 2^1_000_000), u64", |b| b.iter(|| black_box(&n).to_decimal()));
}

criterion_group!(benches, bench_to_decimal);
