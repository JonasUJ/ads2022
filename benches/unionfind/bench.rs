use ads2022::unionfind::{read_test_file, UnionFind};
use criterion::{criterion_group, criterion_main, BatchSize, Criterion};

macro_rules! bench {
    ($name:literal, $f:expr, $uf:ident, $pairs:ident, $group:ident) => {
        let uf_clone = $uf.clone();
        let pairs_clone = $pairs.clone();
        $group.bench_function($name, move |b| {
            b.iter_batched(
                || uf_clone.clone(),
                |mut uf| {
                    for (a, b) in &pairs_clone {
                        uf.union_generic(*a, *b, &$f);
                    }
                },
                BatchSize::SmallInput,
            )
        });
    };
}

pub fn unionfind_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("unionfind");

    let (uf, pairs) = read_test_file("./benches/unionfind/mediumUF.txt");

    // Bench standard "find" differently because it uses `union` (as opposed to `union_generic`)
    let uf_clone = uf.clone();
    let pairs_clone = pairs.clone();
    group.bench_function("find", move |b| {
        b.iter_batched(
            || uf_clone.clone(),
            |mut uf| {
                for (a, b) in &pairs_clone {
                    uf.union(*a, *b);
                }
            },
            BatchSize::SmallInput,
        )
    });

    // bench!("find", UnionFind::find, uf, pairs, group);
    bench!("find_plain", UnionFind::find_plain, uf, pairs, group);
    bench!(
        "find_plain_safe",
        UnionFind::find_plain_safe,
        uf,
        pairs,
        group
    );
    bench!("find_compress", UnionFind::find_compress, uf, pairs, group);
    bench!(
        "find_compress_safe",
        UnionFind::find_compress_safe,
        uf,
        pairs,
        group
    );
    bench!(
        "find_compress_one",
        UnionFind::find_compress_one,
        uf,
        pairs,
        group
    );
    bench!(
        "find_compress_one_safe",
        UnionFind::find_compress_one_safe,
        uf,
        pairs,
        group
    );
    bench!(
        "find_compress_one_do_while",
        UnionFind::find_compress_one_do_while,
        uf,
        pairs,
        group
    );
    bench!(
        "find_compress_one_do_while_safe",
        UnionFind::find_compress_one_do_while_safe,
        uf,
        pairs,
        group
    );
}

criterion_group!(benches, unionfind_benchmark);
criterion_main!(benches);
