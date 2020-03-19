#![cfg_attr(feature = "fail-on-warnings", deny(warnings))]

use criterion::{
    black_box, criterion_group, criterion_main, Bencher, Benchmark, Criterion, Throughput,
};
use num_traits::{One, Zero};
use rand::{
    distributions::{Distribution, Standard},
    Rng,
};
use rand_xoshiro::{rand_core::SeedableRng, Xoshiro256Plus};
use std::convert::TryInto;
use substrate_fixed::{traits::Fixed, types::*};

const SEED: u64 = 42_069;
const DATASET_SIZE: usize = 10_000;

fn gen_non_zero<T, R>(rng: &mut R) -> T
where
    R: Rng + ?Sized,
    T: Zero + One + PartialEq,
    Standard: Distribution<T>,
{
    let value: T = rng.gen();
    if value != T::zero() {
        value
    } else {
        T::one()
    }
}

fn gen_tuple_dataset<T>(cap: usize) -> Vec<(T, T)>
where
    T: Zero + One + PartialEq,
    Standard: Distribution<T>,
{
    let mut rng: Xoshiro256Plus = Xoshiro256Plus::seed_from_u64(SEED);
    (0..cap)
        .map(|_| (rng.gen(), gen_non_zero(&mut rng)))
        .collect()
}

fn fixed_point_op<F, O>(bencher: &mut Bencher, op: O)
where
    F: Fixed,
    F::Bits: Zero + One + PartialEq,
    Standard: Distribution<F::Bits>,
    O: Fn(F, F) -> F,
{
    let bits_dataset: Vec<(F::Bits, F::Bits)> = gen_tuple_dataset(DATASET_SIZE);
    let fixed_dataset: Vec<(F, F)> = bits_dataset
        .into_iter()
        .map(|(l, r)| (Fixed::from_bits(l), Fixed::from_bits(r)))
        .collect();

    bencher.iter(|| {
        for (l, r) in &fixed_dataset {
            let r = op(*l, *r);
            black_box(r);
        }
    });
}

fn primitive_op<P, O>(b: &mut Bencher, op: O)
where
    Standard: Distribution<P>,
    P: Copy + PartialEq + Zero + One,
    O: Fn(P, P) -> P,
{
    let primitive_dataset: Vec<(P, P)> = gen_tuple_dataset(DATASET_SIZE);

    b.iter(|| {
        for (l, r) in &primitive_dataset {
            let sum = op(*l, *r);
            black_box(sum);
        }
    });
}

macro_rules! create_bench {
    ($bench:ident, $name:expr, $op:expr) => {
        pub(crate) fn $bench(c: &mut Criterion) {
            c.bench(
                &$name.to_owned(),
                // We only measure the overhead for the 64 bit test because
                // we found that the overhead is consistant accross sizes.
                Benchmark::new("benchmark overhead", move |b| {
                    let f64_dataset: Vec<(f64, f64)> = gen_tuple_dataset(DATASET_SIZE);
                    b.iter(|| {
                        for (l, _) in &f64_dataset {
                            black_box(l);
                        }
                    });
                })
                .with_function("u128", move |b| {
                    primitive_op::<u128, _>(b, $op);
                })
                .with_function("i128", move |b| {
                    primitive_op::<i128, _>(b, $op);
                })
                .with_function("FixedU128", move |b| {
                    fixed_point_op::<U64F64, _>(b, $op);
                })
                .with_function("FixedI128", move |b| {
                    fixed_point_op::<I64F64, _>(b, $op);
                })
                .with_function("f64", move |b| {
                    primitive_op::<f64, _>(b, $op);
                })
                .with_function("u64", move |b| {
                    primitive_op::<u64, _>(b, $op);
                })
                .with_function("i64", move |b| {
                    primitive_op::<i64, _>(b, $op);
                })
                .with_function("FixedU64", move |b| {
                    fixed_point_op::<U32F32, _>(b, $op);
                })
                .with_function("FixedI64", move |b| {
                    fixed_point_op::<I32F32, _>(b, $op);
                })
                .with_function("f32", move |b| {
                    primitive_op::<f32, _>(b, $op);
                })
                .with_function("u32", move |b| {
                    primitive_op::<u32, _>(b, $op);
                })
                .with_function("i32", move |b| {
                    primitive_op::<i32, _>(b, $op);
                })
                .with_function("FixedU32", move |b| {
                    fixed_point_op::<U16F16, _>(b, $op);
                })
                .with_function("FixedI32", move |b| {
                    fixed_point_op::<I16F16, _>(b, $op);
                })
                .with_function("u16", move |b| {
                    primitive_op::<u16, _>(b, $op);
                })
                .with_function("i16", move |b| {
                    primitive_op::<i16, _>(b, $op);
                })
                .with_function("FixedU16", move |b| {
                    fixed_point_op::<U8F8, _>(b, $op);
                })
                .with_function("FixedI16", move |b| {
                    fixed_point_op::<I8F8, _>(b, $op);
                })
                .with_function("u8", move |b| {
                    primitive_op::<u8, _>(b, $op);
                })
                .with_function("i8", move |b| {
                    primitive_op::<i8, _>(b, $op);
                })
                .with_function("FixedU8", move |b| {
                    fixed_point_op::<U4F4, _>(b, $op);
                })
                .with_function("FixedI8", move |b| {
                    fixed_point_op::<I4F4, _>(b, $op);
                })
                .throughput(Throughput::Elements(DATASET_SIZE.try_into().unwrap())),
            );
        }
    };
}

create_bench!(bench_add, "add", |l, r| l + r);
create_bench!(bench_sub, "sub", |l, r| l - r);
create_bench!(bench_mul, "mul", |l, r| l * r);
create_bench!(bench_div, "div", |l, r| l / r);

criterion_group!(benches, bench_add, bench_sub, bench_mul, bench_div);
criterion_main!(benches);
