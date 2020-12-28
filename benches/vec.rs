use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

fn bench_push(c: &mut Criterion) {
    let mut group = c.benchmark_group("N x push");

    for n in [100usize, 1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("Bonifacio<String>", n), n, |b, &n| {
            b.iter(|| {
                let mut v = bonifacio::Vec::new_unsized();
                for i in 0..n {
                    v.push(black_box(format!("Value #{}", i)));
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("Standard<String>", n), n, |b, &n| {
            b.iter(|| {
                let mut v = Vec::new();
                for i in 0..n {
                    v.push(black_box(format!("Value #{}", i)));
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("Bonifacio<usize>", n), n, |b, &n| {
            b.iter(|| {
                let mut v = bonifacio::Vec::new_sized();
                for i in 0..n {
                    v.push(black_box(i));
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("Standard<usize>", n), n, |b, &n| {
            b.iter(|| {
                let mut v = Vec::new();
                for i in 0..n {
                    v.push(black_box(i));
                }
            })
        });
    }

    group.finish();
}

fn bench_get(c: &mut Criterion) {
    let mut group = c.benchmark_group("N x get");

    for n in [100usize, 1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("Bonifacio<String>", n), n, |b, &n| {
            let mut v = bonifacio::Vec::new_unsized();
            for i in 0..n {
                v.push(format!("Value #{}", i));
            }

            b.iter(|| {
                for i in 0..n {
                    v.get(black_box(i)).unwrap();
                }
            })
        });

        group.bench_with_input(
            BenchmarkId::new("Bonifacio<String> (Borrow)", n),
            n,
            |b, &n| {
                let mut v = bonifacio::Vec::new_unsized();
                for i in 0..n {
                    v.push(format!("Value #{}", i));
                }

                b.iter(|| {
                    for i in 0..n {
                        v.borrow(black_box(i)).unwrap();
                    }
                })
            },
        );

        group.bench_with_input(BenchmarkId::new("Standard<String>", n), n, |b, &n| {
            let mut v = Vec::new();
            for i in 0..n {
                v.push(format!("Value #{}", i));
            }

            b.iter(|| {
                for i in 0..n {
                    v.get(black_box(i)).unwrap();
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("Bonifacio<usize>", n), n, |b, &n| {
            let mut v = bonifacio::Vec::new_sized();
            for i in 0..n {
                v.push(i);
            }

            b.iter(|| {
                for i in 0..n {
                    v.get(black_box(i)).unwrap();
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("Standard<usize>", n), n, |b, &n| {
            let mut v = Vec::new();
            for i in 0..n {
                v.push(i);
            }

            b.iter(|| {
                for i in 0..n {
                    v.get(black_box(i)).unwrap();
                }
            })
        });
    }

    group.finish();
}

fn bench_combination(c: &mut Criterion) {
    let mut group = c.benchmark_group("N x push -> N/2 x insert -> N/2 x remove -> N/2 x push");

    for n in [100usize, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("Bonifacio<String>", n), n, |b, &n| {
            b.iter(|| {
                let mut v = bonifacio::Vec::new_unsized();

                for i in 0..n {
                    v.push(black_box(format!("Value #{}", i)));
                }

                for i in 0..(n / 2) {
                    v.insert(2 * i, black_box(format!("Longer value #{}", i)));
                }

                for i in 0..(n / 2) {
                    v.remove(black_box(2 * i + 1));
                }

                for i in 0..(n / 2) {
                    v.push(black_box(format!("Extra value #{}", i)));
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("Standard<String>", n), n, |b, &n| {
            b.iter(|| {
                let mut v = Vec::new();

                for i in 0..n {
                    v.push(black_box(format!("Value #{}", i)));
                }

                for i in 0..(n / 2) {
                    v.insert(2 * i, black_box(format!("Longer value #{}", i)));
                }

                for i in 0..(n / 2) {
                    v.remove(black_box(2 * i + 1));
                }

                for i in 0..(n / 2) {
                    v.push(black_box(format!("Extra value #{}", i)));
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("Bonifacio<usize>", n), n, |b, &n| {
            b.iter(|| {
                let mut v = bonifacio::Vec::new_sized();

                for i in 0..n {
                    v.push(black_box(i));
                }

                for i in 0..(n / 2) {
                    v.insert(2 * i, black_box(i));
                }

                for i in 0..(n / 2) {
                    v.remove(black_box(2 * i + 1));
                }

                for i in 0..(n / 2) {
                    v.push(black_box(i));
                }
            })
        });

        group.bench_with_input(BenchmarkId::new("Standard<usize>", n), n, |b, &n| {
            b.iter(|| {
                let mut v = Vec::new();

                for i in 0..n {
                    v.push(black_box(i));
                }

                for i in 0..(n / 2) {
                    v.insert(2 * i, black_box(i));
                }

                for i in 0..(n / 2) {
                    v.remove(black_box(2 * i + 1));
                }

                for i in 0..(n / 2) {
                    v.push(black_box(i));
                }
            })
        });
    }

    group.finish();
}

criterion_group!(benches, bench_push, bench_get, bench_combination);
criterion_main!(benches);
