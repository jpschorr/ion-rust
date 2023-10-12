use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ion_rs::{LassoTable, SymbolTable};
use ion_rs::{SymbolArena, SymbolLookup, SymbolRefTable};
use std::time::Duration;

fn data() -> Vec<String> {
    let strs = ["foo", "bar", "baz"];
    let nums: Vec<_> = (1..=1250).collect();
    let mut data = vec![];
    for n in nums {
        for s in strs {
            data.push(format!("{}{}", s, n));
        }
    }

    data
}

fn bench_symtab(c: &mut Criterion) {
    let strs = data();

    c.bench_function("SymbolTable populate", |b| {
        b.iter(|| {
            let mut symtab = SymbolTable::default();
            for d in &strs {
                symtab.intern(black_box(d));
            }
        })
    });

    c.bench_function("SymbolArena populate", |b| {
        b.iter(|| {
            let mut symarena = SymbolArena::new();
            for d in &strs {
                (symarena, _) = symarena.intern(black_box(d).as_str());
            }
        })
    });

    c.bench_function("SymbolRefTable populate", |b| {
        b.iter(|| {
            let mut symbolreft = SymbolRefTable::new();
            for d in &strs {
                symbolreft.intern(black_box(d).as_str());
            }
        })
    });

    c.bench_function("LassoTable populate", |b| {
        b.iter(|| {
            let mut lassotab = LassoTable::new();
            for d in &strs {
                lassotab.intern(black_box(d).as_str());
            }
        })
    });

    let mut symtab = SymbolTable::default();
    for d in &strs {
        symtab.intern(black_box(d));
    }

    let mut symarena = SymbolArena::new();
    for d in &strs {
        (symarena, _) = symarena.intern(black_box(d).as_str());
    }

    let mut symbolreft = SymbolRefTable::new();
    for d in &strs {
        symbolreft.intern(black_box(d).as_str());
    }

    let mut lassotab = LassoTable::new();
    for d in &strs {
        lassotab.intern(black_box(d).as_str());
    }

    for d in &strs {
        //dbg!(d);
        let exemplar = symtab.sid_for(d);
        assert_eq!(exemplar, symarena.sid_for(d));
        assert_eq!(exemplar, symbolreft.sid_for(d));
        assert_eq!(exemplar, lassotab.sid_for(d));
    }

    for id in 1..strs.len() {
        let exemplar = symtab.text_for(id);
        assert_eq!(exemplar, symarena.text_for(id));
        assert_eq!(exemplar, symbolreft.text_for(id));
        assert_eq!(exemplar, lassotab.text_for(id));
    }

    c.bench_function("SymbolTable sid_for", |b| {
        b.iter(|| {
            for d in &strs {
                symtab.sid_for(black_box(d));
            }
        })
    });

    c.bench_function("SymbolArena sid_for", |b| {
        b.iter(|| {
            for d in &strs {
                symarena.sid_for(black_box(d));
            }
        })
    });

    c.bench_function("SymbolRefTable sid_for", |b| {
        b.iter(|| {
            for d in &strs {
                symbolreft.sid_for(black_box(d));
            }
        })
    });

    c.bench_function("LassoTable sid_for", |b| {
        b.iter(|| {
            for d in &strs {
                lassotab.sid_for(black_box(d));
            }
        })
    });

    c.bench_function("SymbolTable text_for", |b| {
        b.iter(|| {
            for id in 1..strs.len() {
                black_box(symtab.text_for(black_box(id)));
            }
        })
    });

    c.bench_function("SymbolArena text_for", |b| {
        b.iter(|| {
            for id in 1..strs.len() {
                black_box(symarena.text_for(black_box(id)));
            }
        })
    });

    c.bench_function("SymbolRefTable text_for", |b| {
        b.iter(|| {
            for id in 1..strs.len() {
                black_box(symbolreft.text_for(black_box(id)));
            }
        })
    });

    c.bench_function("LassoTable text_for", |b| {
        b.iter(|| {
            for id in 1..strs.len() {
                black_box(lassotab.text_for(black_box(id)));
            }
        })
    });
}

criterion_group! {
    name = symtab;
    config = Criterion::default().measurement_time(Duration::new(5, 0));
    targets = bench_symtab
}

criterion_main!(symtab);
