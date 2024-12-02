/* ************************************************************************ */
/*  */
/* OCaml */
/*  */
/* Simon Cruanes */
/*  */
/* Copyright 2017 Institut National de Recherche en Informatique et */
/* en Automatique. */
/*  */
/* All rights reserved.  This file is distributed under the terms of */
/* the GNU Lesser General Public License version 2.1, with the */
/* special exception on linking described in the file LICENSE. */
/*  */
/* ************************************************************************ */

/* Module [Seq]: functional iterators */

type rec node<+'a> =
  | Nil
  | Cons('a, t<'a>)

and t<'a> = unit => node<'a>

let empty = () => Nil

let return = (x, ()) => Cons(x, empty)

let cons = (x, next, ()) => Cons(x, next)

let rec append = (seq1, seq2, ()) =>
  switch seq1() {
  | Nil => seq2()
  | Cons(x, next) => Cons(x, append(next, seq2))
  }

let rec map = (f, seq, ()) =>
  switch seq() {
  | Nil => Nil
  | Cons(x, next) => Cons(f(x), map(f, next))
  }

let rec filter_map = (f, seq, ()) =>
  switch seq() {
  | Nil => Nil
  | Cons(x, next) =>
    switch f(x) {
    | None => filter_map(f, next, ())
    | Some(y) => Cons(y, filter_map(f, next))
    }
  }

let rec filter = (f, seq, ()) =>
  switch seq() {
  | Nil => Nil
  | Cons(x, next) =>
    if f(x) {
      Cons(x, filter(f, next))
    } else {
      filter(f, next, ())
    }
  }

let rec concat = (seq, ()) =>
  switch seq() {
  | Nil => Nil
  | Cons(x, next) => append(x, concat(next), ())
  }

let rec flat_map = (f, seq, ()) =>
  switch seq() {
  | Nil => Nil
  | Cons(x, next) => append(f(x), flat_map(f, next), ())
  }

let concat_map = flat_map

let rec fold_left = (f, acc, seq) =>
  switch seq() {
  | Nil => acc
  | Cons(x, next) =>
    let acc = f(acc, x)
    fold_left(f, acc, next)
  }

let rec iter = (f, seq) =>
  switch seq() {
  | Nil => ()
  | Cons(x, next) =>
    f(x)
    iter(f, next)
  }

let rec unfold = (f, u, ()) =>
  switch f(u) {
  | None => Nil
  | Some(x, u') => Cons(x, unfold(f, u'))
  }

let is_empty = xs =>
  switch xs() {
  | Nil => true
  | Cons(_, _) => false
  }

let uncons = xs =>
  switch xs() {
  | Cons(x, xs) => Some(x, xs)
  | Nil => None
  }

let rec length_aux = (accu, xs) =>
  switch xs() {
  | Nil => accu
  | Cons(_, xs) => length_aux(accu + 1, xs)
  }

@inline let length = xs => length_aux(0, xs)

let rec iteri_aux = (f, i, xs) =>
  switch xs() {
  | Nil => ()
  | Cons(x, xs) =>
    f(i, x)
    iteri_aux(f, i + 1, xs)
  }

@inline let iteri = (f, xs) => iteri_aux(f, 0, xs)

let rec fold_lefti_aux = (f, accu, i, xs) =>
  switch xs() {
  | Nil => accu
  | Cons(x, xs) =>
    let accu = f(accu, i, x)
    fold_lefti_aux(f, accu, i + 1, xs)
  }

@inline let fold_lefti = (f, accu, xs) => fold_lefti_aux(f, accu, 0, xs)

let rec for_all = (p, xs) =>
  switch xs() {
  | Nil => true
  | Cons(x, xs) => p(x) && for_all(p, xs)
  }

let rec exists = (p, xs) =>
  switch xs() {
  | Nil => false
  | Cons(x, xs) => p(x) || exists(p, xs)
  }

let rec find = (p, xs) =>
  switch xs() {
  | Nil => None
  | Cons(x, xs) =>
    if p(x) {
      Some(x)
    } else {
      find(p, xs)
    }
  }

let rec find_map = (f, xs) =>
  switch xs() {
  | Nil => None
  | Cons(x, xs) =>
    switch f(x) {
    | None => find_map(f, xs)
    | Some(_) as result => result
    }
  }

/* [iter2], [fold_left2], [for_all2], [exists2], [map2], [zip] work also in
   the case where the two sequences have different lengths. They stop as soon
   as one sequence is exhausted. Their behavior is slightly asymmetric: when
   [xs] is empty, they do not force [ys]; however, when [ys] is empty, [xs] is
   forced, even though the result of the function application [xs()] turns out
   to be useless. */

let rec iter2 = (f, xs, ys) =>
  switch xs() {
  | Nil => ()
  | Cons(x, xs) =>
    switch ys() {
    | Nil => ()
    | Cons(y, ys) =>
      f(x, y)
      iter2(f, xs, ys)
    }
  }

let rec fold_left2 = (f, accu, xs, ys) =>
  switch xs() {
  | Nil => accu
  | Cons(x, xs) =>
    switch ys() {
    | Nil => accu
    | Cons(y, ys) =>
      let accu = f(accu, x, y)
      fold_left2(f, accu, xs, ys)
    }
  }

let rec for_all2 = (f, xs, ys) =>
  switch xs() {
  | Nil => true
  | Cons(x, xs) =>
    switch ys() {
    | Nil => true
    | Cons(y, ys) => f(x, y) && for_all2(f, xs, ys)
    }
  }

let rec exists2 = (f, xs, ys) =>
  switch xs() {
  | Nil => false
  | Cons(x, xs) =>
    switch ys() {
    | Nil => false
    | Cons(y, ys) => f(x, y) || exists2(f, xs, ys)
    }
  }

let rec equal = (eq, xs, ys) =>
  switch (xs(), ys()) {
  | (Nil, Nil) => true
  | (Cons(x, xs), Cons(y, ys)) => eq(x, y) && equal(eq, xs, ys)
  | (Nil, Cons(_, _))
  | (Cons(_, _), Nil) => false
  }

let rec compare = (cmp, xs, ys) =>
  switch (xs(), ys()) {
  | (Nil, Nil) => 0
  | (Cons(x, xs), Cons(y, ys)) =>
    let c = cmp(x, y)
    if c != 0 {
      c
    } else {
      compare(cmp, xs, ys)
    }
  | (Nil, Cons(_, _)) => -1
  | (Cons(_, _), Nil) => 1
  }

/* [init_aux f i j] is the sequence [f i, ..., f (j-1)]. */

let rec init_aux = (f, i, j, ()) =>
  if i < j {
    Cons(f(i), init_aux(f, i + 1, j))
  } else {
    Nil
  }

let init = (n, f) =>
  if n < 0 {
    invalid_arg("Seq.init")
  } else {
    init_aux(f, 0, n)
  }

let rec repeat = (x, ()) => Cons(x, repeat(x))

let rec forever = (f, ()) => Cons(f(), forever(f))

/* This preliminary definition of [cycle] requires the sequence [xs]
   to be nonempty. Applying it to an empty sequence would produce a
   sequence that diverges when it is forced. */

let rec cycle_nonempty = (xs, ()) => append(xs, cycle_nonempty(xs), ())

/* [cycle xs] checks whether [xs] is empty and, if so, returns an empty
   sequence. Otherwise, [cycle xs] produces one copy of [xs] followed
   with the infinite sequence [cycle_nonempty xs]. Thus, the nonemptiness
   check is performed just once. */

let cycle = (xs, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs') => Cons(x, append(xs', cycle_nonempty(xs)))
  }

/* [iterate1 f x] is the sequence [f x, f (f x), ...].
   It is equivalent to [tail (iterate f x)].
   [iterate1] is used as a building block in the definition of [iterate]. */

let rec iterate1 = (f, x, ()) => {
  let y = f(x)
  Cons(y, iterate1(f, y))
}

/* [iterate f x] is the sequence [x, f x, ...]. */

/* The reason why we give this slightly indirect definition of [iterate],
   as opposed to the more naive definition that may come to mind, is that
   we are careful to avoid evaluating [f x] until this function call is
   actually necessary. The naive definition (not shown here) computes the
   second argument of the sequence, [f x], when the first argument is
   requested by the user. */

let iterate = (f, x) => cons(x, iterate1(f, x))

let rec mapi_aux = (f, i, xs, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) => Cons(f(i, x), mapi_aux(f, i + 1, xs))
  }

@inline let mapi = (f, xs) => mapi_aux(f, 0, xs)

/* [tail_scan f s xs] is equivalent to [tail (scan f s xs)].
 [tail_scan] is used as a building block in the definition of [scan]. */

/* This slightly indirect definition of [scan] is meant to avoid computing
 elements too early; see the above comment about [iterate1] and [iterate]. */

let rec tail_scan = (f, s, xs, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) =>
    let s = f(s, x)
    Cons(s, tail_scan(f, s, xs))
  }

let scan = (f, s, xs) => cons(s, tail_scan(f, s, xs))

/* [take] is defined in such a way that [take 0 xs] returns [empty]
 immediately, without allocating any memory. */

let rec take_aux = (n, xs) =>
  if n == 0 {
    empty
  } else {
    () =>
      switch xs() {
      | Nil => Nil
      | Cons(x, xs) => Cons(x, take_aux(n - 1, xs))
      }
  }

let take = (n, xs) => {
  if n < 0 {
    invalid_arg("Seq.take")
  }
  take_aux(n, xs)
}

/* [force_drop n xs] is equivalent to [drop n xs ()].
   [force_drop n xs] requires [n > 0].
   [force_drop] is used as a building block in the definition of [drop]. */

let rec force_drop = (n, xs) =>
  switch xs() {
  | Nil => Nil
  | Cons(_, xs) =>
    let n = n - 1
    if n == 0 {
      xs()
    } else {
      force_drop(n, xs)
    }
  }

/* [drop] is defined in such a way that [drop 0 xs] returns [xs] immediately,
 without allocating any memory. */

let drop = (n, xs) =>
  if n < 0 {
    invalid_arg("Seq.drop")
  } else if n == 0 {
    xs
  } else {
    () => force_drop(n, xs)
  }

let rec take_while = (p, xs, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) =>
    if p(x) {
      Cons(x, take_while(p, xs))
    } else {
      Nil
    }
  }

let rec drop_while = (p, xs, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) as node =>
    if p(x) {
      drop_while(p, xs, ())
    } else {
      node
    }
  }

let rec group = (eq, xs, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) => Cons(cons(x, take_while(eq(x), xs)), group(eq, drop_while(eq(x), xs)))
  }

exception Forced_twice

module Suspension = {
  type suspension<'a> = unit => 'a

  /* Conversions. */

  let to_lazy: suspension<'a> => Lazy.t<'a> = Lazy.from_fun
  /* fun s -> lazy (s()) */

  let from_lazy = (s: Lazy.t<'a>): suspension<'a> => () => Lazy.force(s)

  /* [memoize] turns an arbitrary suspension into a persistent suspension. */

  let memoize = (s: suspension<'a>): suspension<'a> => from_lazy(to_lazy(s))

  /* [failure] is a suspension that fails when forced. */

  /* let failure : _ suspension = */
  /* fun () -> */
  /* A suspension created by [once] has been forced twice. */
  /* raise Forced_twice */

  /* If [f] is a suspension, then [once f] is a suspension that can be forced
     at most once. If it is forced more than once, then [Forced_twice] is
     raised. */

  /* let once (f : 'a suspension) : 'a suspension = */
  /* let action = Atomic.make f in */
  /* fun () -> */
  /* Get the function currently stored in [action], and write the
         function [failure] in its place, so the next access will result
         in a call to [failure()]. */
  /* let f = Atomic.exchange action failure in */
  /* f() */
} /* Suspension */

let rec memoize = xs =>
  Suspension.memoize(() =>
    switch xs() {
    | Nil => Nil
    | Cons(x, xs) => Cons(x, memoize(xs))
    }
  )

/* let rec once xs = */
/* Suspension.once (fun () -> */
/* match xs() with */
/* | Nil -> */
/* Nil */
/* | Cons (x, xs) -> */
/* Cons (x, once xs) */
/* ) */

let rec zip = (xs, ys, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) =>
    switch ys() {
    | Nil => Nil
    | Cons(y, ys) => Cons((x, y), zip(xs, ys))
    }
  }

let rec map2 = (f, xs, ys, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) =>
    switch ys() {
    | Nil => Nil
    | Cons(y, ys) => Cons(f(x, y), map2(f, xs, ys))
    }
  }

let rec interleave = (xs, ys, ()) =>
  switch xs() {
  | Nil => ys()
  | Cons(x, xs) => Cons(x, interleave(ys, xs))
  }

/* [sorted_merge1l cmp x xs ys] is equivalent to
     [sorted_merge cmp (cons x xs) ys].

   [sorted_merge1r cmp xs y ys] is equivalent to
     [sorted_merge cmp xs (cons y ys)].

   [sorted_merge1 cmp x xs y ys] is equivalent to
     [sorted_merge cmp (cons x xs) (cons y ys)].

   These three functions are used as building blocks in the definition
   of [sorted_merge]. */

let rec sorted_merge1l = (cmp, x, xs, ys, ()) =>
  switch ys() {
  | Nil => Cons(x, xs)
  | Cons(y, ys) => sorted_merge1(cmp, x, xs, y, ys)
  }

and sorted_merge1r = (cmp, xs, y, ys, ()) =>
  switch xs() {
  | Nil => Cons(y, ys)
  | Cons(x, xs) => sorted_merge1(cmp, x, xs, y, ys)
  }

and sorted_merge1 = (cmp, x, xs, y, ys) =>
  if cmp(x, y) <= 0 {
    Cons(x, sorted_merge1r(cmp, xs, y, ys))
  } else {
    Cons(y, sorted_merge1l(cmp, x, xs, ys))
  }

let sorted_merge = (cmp, xs, ys, ()) =>
  switch (xs(), ys()) {
  | (Nil, Nil) => Nil
  | (Nil, c)
  | (c, Nil) => c
  | (Cons(x, xs), Cons(y, ys)) => sorted_merge1(cmp, x, xs, y, ys)
  }

let rec map_fst = (xys, ()) =>
  switch xys() {
  | Nil => Nil
  | Cons((x, _), xys) => Cons(x, map_fst(xys))
  }

let rec map_snd = (xys, ()) =>
  switch xys() {
  | Nil => Nil
  | Cons((_, y), xys) => Cons(y, map_snd(xys))
  }

let unzip = xys => (map_fst(xys), map_snd(xys))

let split = unzip

/* [filter_map_find_left_map f xs] is equivalent to
 [filter_map Either.find_left (map f xs)]. */

let rec filter_map_find_left_map = (f, xs, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) =>
    switch f(x) {
    | Either.Left(y) => Cons(y, filter_map_find_left_map(f, xs))
    | Either.Right(_) => filter_map_find_left_map(f, xs, ())
    }
  }

let rec filter_map_find_right_map = (f, xs, ()) =>
  switch xs() {
  | Nil => Nil
  | Cons(x, xs) =>
    switch f(x) {
    | Either.Left(_) => filter_map_find_right_map(f, xs, ())
    | Either.Right(z) => Cons(z, filter_map_find_right_map(f, xs))
    }
  }

let partition_map = (f, xs) => (filter_map_find_left_map(f, xs), filter_map_find_right_map(f, xs))

let partition = (p, xs) => (filter(p, xs), filter(x => !p(x), xs))

/* If [xss] is a matrix (a sequence of rows), then [peel xss] is a pair of
   the first column (a sequence of elements) and of the remainder of the
   matrix (a sequence of shorter rows). These two sequences have the same
   length. The rows of the matrix [xss] are not required to have the same
   length. An empty row is ignored. */

/* Because [peel] uses [unzip], its argument must be persistent. The same
 remark applies to [transpose], [diagonals], [product], etc. */

let peel = xss => unzip(filter_map(uncons, xss))

let rec transpose = (xss, ()) => {
  let (heads, tails) = peel(xss)
  if is_empty(heads) {
    assert is_empty(tails)
    Nil
  } else {
    Cons(heads, transpose(tails))
  }
}

/* The internal function [diagonals] takes an extra argument, [remainders],
   which contains the remainders of the rows that have already been
   discovered. */

let rec diagonals = (remainders, xss, ()) =>
  switch xss() {
  | Cons(xs, xss) =>
    switch xs() {
    | Cons(x, xs) =>
      /* We discover a new nonempty row [x :: xs]. Thus, the next diagonal
             is [x :: heads]: this diagonal begins with [x] and continues with
             the first element of every row in [remainders]. In the recursive
             call, the argument [remainders] is instantiated with [xs ::
             tails], which means that we have one more remaining row, [xs],
             and that we keep the tails of the pre-existing remaining rows. */
      let (heads, tails) = peel(remainders)
      Cons(cons(x, heads), diagonals(cons(xs, tails), xss))
    | Nil =>
      /* We discover a new empty row. In this case, the new diagonal is
             just [heads], and [remainders] is instantiated with just [tails],
             as we do not have one more remaining row. */
      let (heads, tails) = peel(remainders)
      Cons(heads, diagonals(tails, xss))
    }
  | Nil =>
    /* There are no more rows to be discovered. There remains to exhaust
     the remaining rows. */
    transpose(remainders, ())
  }

/* If [xss] is a matrix (a sequence of rows), then [diagonals xss] is
   the sequence of its diagonals.

   The first diagonal contains just the first element of the
   first row. The second diagonal contains the first element of the
   second row and the second element of the first row; and so on.
   This kind of diagonal is in fact sometimes known as an antidiagonal.

   - Every diagonal is a finite sequence.
   - The rows of the matrix [xss] are not required to have the same length.
   - The matrix [xss] is not required to be finite (in either direction).
   - The matrix [xss] must be persistent. */

let diagonals = xss => diagonals(empty, xss)

let map_product = (f, xs, ys) => concat(diagonals(map(x => map(y => f(x, y), ys), xs)))

let product = (xs, ys) => map_product((x, y) => (x, y), xs, ys)

let of_dispenser = it => {
  let rec c = () =>
    switch it() {
    | None => Nil
    | Some(x) => Cons(x, c)
    }

  c
}

let to_dispenser = xs => {
  let s = ref(xs)
  () =>
    switch s.contents() {
    | Nil => None
    | Cons(x, xs) =>
      s := xs
      Some(x)
    }
}

let rec ints = (i, ()) => Cons(i, ints(i + 1))
