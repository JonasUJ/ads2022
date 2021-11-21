use ads2022::sort::*;
use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

macro_rules! bench {
    ($name:literal, $sort:ident, $unsorted:ident, $group:ident) => {
        let unsorted_clone = $unsorted.clone();
        $group.bench_function($name, move |b| {
            b.iter_batched(
                || unsorted_clone.clone(),
                |mut unsorted| {
                    $sort::sort(&mut unsorted);
                },
                BatchSize::SmallInput,
            )
        });
    };
}

pub fn sort_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("sort");

    let unsorted = read_test_file("./benches/sort/sort2k.txt");

    let unsorted_clone = unsorted.clone();
    group.bench_function("std_sort", move |b| {
        b.iter_batched(
            || unsorted_clone.clone(),
            |mut unsorted| {
                unsorted.sort_unstable();
            },
            BatchSize::SmallInput,
        )
    });

    bench!("selection_sort", Selection, unsorted, group);
    bench!("swap_insertion_sort", SwapInsertion, unsorted, group);
    bench!("insertion_sort", Insertion, unsorted, group);
    bench!("shell_sort", Shell, unsorted, group);
    bench!("merge_sort", Merge, unsorted, group);
    bench!("merge_fallback_sort", MergeFallback, unsorted, group);
    bench!("iterative_merge_sort", IterativeMerge, unsorted, group);
    bench!("quick_sort", Quick, unsorted, group);
    bench!("quick_fallback_sort", QuickFallback, unsorted, group);
}

criterion_group!(benches, sort_benchmark);
criterion_main!(benches);
