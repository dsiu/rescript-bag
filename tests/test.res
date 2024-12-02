module I = {
  type t = int
  let compare = Pervasives.compare
}

module B = Bag.Make(I)

/* let print = B.print Format.pp_print_int */

let () = {
  let a = B.add(1, ~mult=1, B.add(2, ~mult=2, B.add(3, ~mult=3, B.empty)))
  let b = B.add(1, ~mult=4, B.add(2, ~mult=5, B.add(3, ~mult=6, B.empty)))
  assert (B.cardinal(a) == 6)
  assert (B.cardinal(B.sum(a, b)) == 21)
  assert (B.cardinal(B.union(a, b)) == 15)
  assert B.is_empty(B.diff(a, b))
  assert (B.cardinal(B.diff(b, a)) == 9)
  assert B.equal(B.inter(a, b), a)
  assert B.included(a, b)
  assert !B.included(b, a)
  assert !B.disjoint(b, a)
  assert (B.elements(a) == list{(1, 1), (2, 2), (3, 3)})
  assert (B.min_elt(a) == (1, 1))
  assert (B.max_elt(a) == (3, 3))
  let f = _ => 1
  assert (B.cardinal(B.map(f, a)) == 3)
  assert (B.cardinal(B.map(f, b)) == 3)
  let e = B.filter((x, _) => mod(x, 2) == 0, a)
  assert (B.min_elt(e) == (2, 2))
  assert (B.max_elt(e) == (2, 2))
  assert (B.choose(e) == (2, 2))
  assert (B.cardinal(e) == 2)
  let o = B.filter((x, _) => mod(x, 2) == 1, b)
  assert (B.min_elt(o) == (1, 4))
  assert (B.max_elt(o) == (3, 6))
  assert (B.cardinal(o) == 10)
  ()
}

let test = n => {
  let b1 = ref(B.empty)
  let b2 = ref(B.empty)
  for x in 0 to n {
    b1 := B.add(x, ~mult=2, b1.contents)
    assert (B.cardinal(b1.contents) == 2 * (x + 1))
    b2 := B.add(n - x, b2.contents)
    assert (B.cardinal(b2.contents) == 2 * x + 1)
    b2 := B.add(n - x, b2.contents)
    if x < n / 2 {
      assert B.disjoint(b1.contents, b2.contents)
    }
  }
  assert B.mem(n, b1.contents)
  assert (B.occ(n, b1.contents) == 2)
  assert (B.cardinal(b1.contents) == 2 * (n + 1))
  assert (B.cardinal(b2.contents) == 2 * (n + 1))
  assert B.equal(b1.contents, b2.contents)
  assert B.for_all((x, _) => x <= n, b1.contents)
  assert !B.for_all((x, _) => x < n, b1.contents)
  assert B.exists((x, m) => x == 0 && m == 2, b2.contents)
  for x in 0 to n {
    b1 := B.remove_all(x, b1.contents)
    b2 := B.remove(n - x, ~mult=2, b2.contents)
  }
  assert B.is_empty(b1.contents)
  assert B.is_empty(b2.contents)
  ()
}

let () = for n in 0 to 10 {
  test(10 * n)
}

/* division */

let () = Random.init(42)

let test = n => {
  let b1 = ref(B.empty)
  let b2 = ref(B.empty)
  for i in 0 to n - 1 {
    b1 := B.add(~mult=Random.int(10), i, b1.contents)
    b2 := B.add(~mult=Random.int(3), i, b2.contents)
  }
  let (q, r) = B.div(b1.contents, b2.contents)
  /* Format.printf "b1 = %a / b2 = %a@." print !b1 print !b2;
   * Format.printf "q = %d / r = %a@." q print r; */
  assert B.equal(b1.contents, B.sum(B.mul(b2.contents, q), r))
  let (q, r) = B.divi(b1.contents, 1)
  assert (B.equal(q, b1.contents) && B.is_empty(r))
  for k in 2 to 5 {
    let (q, r) = B.divi(b1.contents, k)
    assert B.equal(b1.contents, B.sum(B.mul(q, k), r))
  }
}

let () = for n in 0 to 10 {
  test(n)
}
