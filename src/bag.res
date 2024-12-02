/* ************************************************************************ */
/*  */
/* Copyright (C) Jean-Christophe Filliatre */
/*  */
/* This software is free software; you can redistribute it and/or */
/* modify it under the terms of the GNU Library General Public */
/* License version 2.1, with the special exception on linking */
/* described in file LICENSE. */
/*  */
/* This software is distributed in the hope that it will be useful, */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. */
/*  */
/* ************************************************************************ */

module Make = (
  X: {
    type t
    let cmp: (t, t) => int
  },
) => {
  module M = Belt.Map
  module KEY = Belt.Id.MakeComparableU(X)

  type elt = X.t
  type t = M.t<KEY.t, int, KEY.identity>

  @ocaml.doc(" invariant: multiplicities are all > 0 ")
  let empty = Belt.Map.make(~id=module(KEY))

  let is_empty = b => M.isEmpty(b)

  let mem = (elt, b) => b->M.has(elt)

  let find = (x, b) => {
    b->M.findFirstBy((k, _) => k == x)
  }

  let occ = (x, b) => {
    find(x, b)->Option.mapOr(0, ((_, v)) => v)
    //    let o = find(x, b)
    //    switch o {
    //    | Some((k, v)) => v
    //    | None => 0
    //    }
  }

  let add = (x, ~mult=1, b) => {
    if mult < 0 {
      invalid_arg("add")
    }
    if mult == 0 {
      b
    } else {
      let m = find(x, b)
      switch m {
      | Some((_, v)) => M.set(b, x, v + mult)
      | None => M.set(b, x, mult)
      }
    }
  }

  let update = (x, f, b) => {
    let f = o => {
      let m = f(
        switch o {
        | None => 0
        | Some(m) => m
        },
      )
      if m < 0 {
        invalid_arg("update")
      }
      if m == 0 {
        None
      } else {
        Some(m)
      }
    }
    M.update(b, x, f)
  }

  let singleton = x => M.set(empty, x, 1)

  let remove = (x, ~mult=1, b) => {
    if mult < 0 {
      invalid_arg("remove")
    }
    if mult == 0 {
      b
    } else {
      M.update(b, x, x =>
        switch x {
        | None | Some(1) => None
        | Some(m) if m <= mult => None
        | Some(m) => Some(m - mult)
        }
      )
    }
  }

  let remove_all = (elt, b) => b->M.remove(elt)

  let merge = (f, b1, b2) => {
    let f = (x, o1, o2) => {
      let m1 = switch o1 {
      | None => 0
      | Some(m) => m
      }
      let m2 = switch o2 {
      | None => 0
      | Some(m) => m
      }
      let m = f(x, m1, m2)
      if m < 0 {
        invalid_arg("merge")
      }
      if m == 0 {
        None
      } else {
        Some(m)
      }
    }
    M.merge(b1, b2, f)
  }

  let cardinal = b => M.reduce(b, 0, (acc, _, m) => m + acc)

  let elements = M.toList(_)

  let min_elt_opt = b => {
    b->M.minKey->Option.map(k => (k, b->M.getExn(k)))
  }

  let min_elt = b => {
    b->min_elt_opt->Option.getExn
  }

  let max_elt_opt = b => {
    b->M.maxKey->Option.map(k => (k, b->M.getExn(k)))
  }

  let max_elt = b => {
    b->max_elt_opt->Option.getExn
  }

  // Not used
  //  let choose = M.choose
  //  let choose_opt = M.choose_opt

  let union = (b1, b2) =>
    M.merge(b1, b2, (_, o1, o2) =>
      switch (o1, o2) {
      | (None, None) => None
      | (None, Some(m)) | (Some(m), None) => Some(m)
      | (Some(m1), Some(m2)) => Some(max(m1, m2))
      }
    )

  let sum = (b1, b2) =>
    M.merge(b1, b2, (_, o1, o2) =>
      switch (o1, o2) {
      | (None, None) => None
      | (None, Some(m)) | (Some(m), None) => Some(m)
      | (Some(m1), Some(m2)) => Some(m1 + m2)
      }
    )

  let inter = (b1, b2) =>
    M.merge(b1, b2, (_, o1, o2) =>
      switch (o1, o2) {
      | (None, None)
      | (None, Some(_))
      | (Some(_), None) =>
        None
      | (Some(m1), Some(m2)) => Some(min(m1, m2))
      }
    )

  let diff = (b1, b2) =>
    M.merge(b1, b2, (_, o1, o2) =>
      switch (o1, o2) {
      | (None, _) => None
      | (Some(m), None) => Some(m)
      | (Some(m1), Some(m2)) if m1 <= m2 => None
      | (Some(m1), Some(m2)) => Some(m1 - m2)
      }
    )

  let disjoint = (b1, b2) => M.every(b1, (x1, _) => !(b2->M.has(x1)))

  let included = (b1, b2) => M.every(b1, (x1, m1) => m1 <= occ(x1, b2))

  let iter = (f, b) => b->M.forEach(f)

  let fold = (f, b, acc) => M.reduce(b, acc, (acc, k, v) => f(k, v, acc))

  let for_all = (f, b) => b->M.every(f)

  let exists = (f, b) => b->M.some(f)

  let filter = (f, b) => b->M.keep(f)

  let partition = (f, b) => b->M.partition(f)

  let split = (x, b) => {
    let ((l, r), m) = M.split(b, x)
    (
      l,
      switch m {
      | None => 0
      | Some(m) => m
      },
      r,
    )
  }

  let find_first_opt = (f, b) => {
    b->M.findFirstBy((k, _) => f(k))
  }

  let find_first = (f, b) => find_first_opt(f, b)->Option.getExn

  // NOT implmented
  //  let find_last = M.find_last
  //  let find_last_opt = M.find_last_opt

  let map = (f, b) => {
    let f = m => {
      let m = f(m)
      if m <= 0 {
        invalid_arg("map")
      }
      m
    }
    b->M.map(f)
  }

  let mapi = (f, b) => {
    let f = (x, m) => {
      let m = f(x, m)
      if m <= 0 {
        invalid_arg("mapi")
      }
      m
    }
    b->M.mapWithKey(f)
  }

  let mul = (b, n) => {
    if n < 0 {
      invalid_arg("mul")
    }
    if n == 0 {
      empty
    } else {
      map(m => m * n, b)
    }
  }

  let div = (b1, b2) =>
    if is_empty(b2) {
      (0, b1)
    } else {
      try {
        let update = (x, m1, q) => {
          let m2 = occ(x, b2)
          if m2 == 0 || m2 > m1 {
            raise(Exit)
          }
          min(q, m1 / m2)
        }
        let q = fold(update, b1, max_int)
        assert(q > 0)
        let remainder = (x, m1, r) => {
          let mult = m1 - q * occ(x, b2)
          add(~mult, x, r)
        }
        let r = fold(remainder, b1, empty)
        (q, r)
      } catch {
      | Exit => (0, b1)
      }
    }

  let divi = (b, n) => {
    if n <= 0 {
      invalid_arg("divi")
    }
    let update = (x, m, (q, r)) => (add(~mult=m / n, x, q), add(~mult=mod(m, n), x, r))
    fold(update, b, (empty, empty))
  }

  let compare = (b1, b2) => M.cmp(b1, b2, (v1, v2) => v2 - v1)
  //(Pervasives.compare)

  let equal = (b1, b2) => M.eq(b1, b2, (v1, v2) => v1 == v2)
  //M.equal(\"==")

  /* let to_seq = */
  /* M.to_seq */

  /* let to_seq_from = */
  /* M.to_seq_from */

  /* let add_seq s b = */
  /* Seq.fold_left (fun b (x, mult) -> add x ~mult b) b s */

  /* let of_seq s = */
  /* add_seq s empty */

  /* let print print_elt fmt b = */
  /* Format.fprintf fmt "{@["; */
  /* let first = ref true in */
  /* iter (fun x m -> */
  /* if not !first then Format.fprintf fmt ","; */
  /* first := false; */
  /* Format.fprintf fmt "@ %a:%d" print_elt x m) b; */
  /* if not !first then Format.fprintf fmt " "; */
  /* Format.fprintf fmt "@]}" */
}
