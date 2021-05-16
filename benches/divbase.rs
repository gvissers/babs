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

use criterion::{Criterion, black_box, criterion_group};
use rand::{Rng, SeedableRng};
use rand::distributions::Standard;
use rand_xoshiro::Xoshiro256PlusPlus;

const DECIMAL_RADIX: u64 = 10_000_000_000_000_000_000;

fn mul_inv_base(n: u128) -> (u64, u64)
{
    // This effectively computes n * ceil(2**192 / 10**19), and the shifts the result 192 bits to
    // the right to compute the quotient q. The remainder is then calculated by subtracting
    // q*10**19 from n. The exponent 192 is high enough that this yields the correct result
    // for all possible n < 10**38. (in fact 188 would suffice). We use an exponent of 192,
    // though, so that the final shift in the calculation of the quotient works out to be 64,
    // which at least on x86_64 removes the need for a shift altogether.
    const SCALE_LOW: u128 = 6225051964306646475;   // scale = (1, SCALE_HIGH, SCALE_LOW) = ceil(2**192 / 10**19)
    const SCALE_HIGH: u128 = 15581492618384294730; // FIXME? this should be calculated from DECIMAL_RADIX
    // The high bit of the scale (1*2**128) is accounted for below in the calculation of
    // quot by the additions of n_low and n_high.

    let (n_low, n_high) = (n & 0xffffffffffffffff, n >> 64);
    let carry = (SCALE_LOW * n_low) >> 64;
    let carry = (SCALE_LOW * n_high + SCALE_HIGH * n_low + carry) >> 64;
    let quot = ((SCALE_HIGH * n_high + carry + n_low) >> 64) + n_high;
    let rem = n - quot * DECIMAL_RADIX as u128;
    (quot as u64, rem as u64)
}

fn mul_inv_base_2(n: u128) -> (u64, u64)
{
    // same idea as above, but with 3 multiplications instead of four.
    const SCALE_LOW: u128 = 11918280793837635165;
    const SCALE_HIGH: u128 = 2126764793255865396;
    const SCALE_SUM: u128 = SCALE_LOW + SCALE_HIGH;

    let (n_low, n_high) = (n & 0xffffffffffffffff, n >> 64);
    let n_sum = n_low + n_high;
    let q0 = SCALE_LOW * n_low;
    let q2 = SCALE_HIGH * n_high;
    let q1 = SCALE_SUM * n_sum - q0 - q2 + (q0 >> 64);
    let quot = (q2 + (q1 >> 64)) >> 60;
    let rem = n - quot * DECIMAL_RADIX as u128;
    (quot as u64, rem as u64)
}

fn div_op_base(n: u128) -> (u64, u64)
{
    let quot = n / DECIMAL_RADIX as u128;
    let rem = n % DECIMAL_RADIX as u128;
    (quot as u64, rem as u64)
}

#[cfg(feature="asm")]
#[inline]
unsafe fn divq(n: u128, d: u64) -> (u64, u64)
{
    let n_low = n as u64;
    let n_high = (n >> 64) as u64;
    let quot: u64;
    let rem: u64;
    asm!(
        "div {0}",
        in(reg) d,
        inlateout("rax") n_low => quot,
        inlateout("rdx") n_high => rem,
        options(pure, nomem, nostack)
    );
    (quot, rem)
}

#[cfg(feature="asm")]
fn divq_base(n: u128) -> (u64, u64)
{
    unsafe { divq(n, DECIMAL_RADIX) }
}

fn div_long_base(n: u128) -> (u64, u64)
{
    let d_high = DECIMAL_RADIX >> 32;

    let n0 = n >> 32;
    let mut q0 = (n0 >> 32) as u64 / d_high;
    let mut qd = q0 as u128 * DECIMAL_RADIX as u128;
    if qd > n0
    {
        q0 -= 1;
        qd -= DECIMAL_RADIX as u128;
        if qd > n0
        {
            q0 -= 1;
            qd -= DECIMAL_RADIX as u128;
        }
    }

    let n1 = ((n0 - qd) << 32) | (n & 0xffffffff);
    let mut q1 = ((n1 >> 32) as u64) / d_high;
    qd = q1 as u128 * DECIMAL_RADIX as u128;
    if qd > n1
    {
        q1 -= 1;
        qd -= DECIMAL_RADIX as u128;
        if qd > n1
        {
            q1 -= 1;
            qd -= DECIMAL_RADIX as u128;
        }
    }

    let rem = (n1 - qd) as u64;
    let quot = (q0 << 32) | q1;

    (quot, rem)
}

fn test_div_base<F>(op: F, nums: &[u128]) -> (u64, u64)
where F: Fn(u128) -> (u64, u64)
{
    nums.iter().fold((0, 0), |(acc_q, acc_r), &n| {
        let (q, r) = op(n);
        (acc_q ^ q, acc_r ^ r)
    })
}

fn bench_div_base(c: &mut Criterion)
{
    let seed: u64 = 0x73927fd352717fd4;
    let nums: Vec<u128> = Xoshiro256PlusPlus::seed_from_u64(seed)
        .sample_iter(Standard)
        .filter(|&n| n < DECIMAL_RADIX as u128 * DECIMAL_RADIX as u128)
        .take(100_000)
        .collect();

    eprintln!("{:?}", test_div_base(mul_inv_base, &nums));
    eprintln!("{:?}", test_div_base(mul_inv_base_2, &nums));
    eprintln!("{:?}", test_div_base(div_op_base, &nums));
    #[cfg(feature="asm")]
    eprintln!("{:?}", test_div_base(divq_base, &nums));
    eprintln!("{:?}", test_div_base(div_long_base, &nums));

    c.bench_function("div base, multiply inverse", |b| b.iter(|| test_div_base(mul_inv_base, black_box(&nums))));
    c.bench_function("div base, multiply inverse 2", |b| b.iter(|| test_div_base(mul_inv_base_2, black_box(&nums))));
    c.bench_function("div base, div operator", |b| b.iter(|| test_div_base(div_op_base, black_box(&nums))));
    #[cfg(feature="asm")]
    c.bench_function("div base, divq instruction", |b| b.iter(|| test_div_base(divq_base, black_box(&nums))));
    c.bench_function("div base, long divison", |b| b.iter(|| test_div_base(div_long_base, black_box(&nums))));
}

criterion_group!(benches, bench_div_base);
