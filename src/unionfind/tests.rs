use super::*;

macro_rules! test_find {
    ($name:ident) => {
        #[test]
        fn $name() {
            let (mut uf, pairs) = read_test_file("./benches/unionfind/mediumUF.txt");
            assert_eq!(uf.find(Site(uf.count())), None);
            for (a, b) in pairs {
                uf.union_generic(a, b, &UnionFind::$name);
            }
            assert_eq!(uf.count(), 3);
        }
    };
}

test_find!(find);
test_find!(find_plain);
test_find!(find_plain_safe);
test_find!(find_compress);
test_find!(find_compress_safe);
test_find!(find_compress_one);
test_find!(find_compress_one_safe);
test_find!(find_compress_one_do_while);
test_find!(find_compress_one_do_while_safe);

#[test]
fn test_union_connects() {
    let mut uf = UnionFind::new(10);
    let a = Site(0);
    let b = Site(8);
    assert!(!uf.connected(a, b));
    uf.union(a, b);
    assert!(uf.connected(a, b));
}

#[test]
fn test_union_lowers_count() {
    let mut uf = UnionFind::new(10);
    let a = Site(0);
    let b = Site(8);
    assert_eq!(uf.count(), 10);
    uf.union(a, b);
    assert_eq!(uf.count(), 9);
}

#[test]
fn test_transitivly_connected() {
    let mut uf = UnionFind::new(10);
    let a = Site(0);
    let b = Site(8);
    let c = Site(4);
    assert!(!uf.connected(b, c));
    uf.union(a, b);
    uf.union(a, c);
    assert!(uf.connected(b, c));
}
