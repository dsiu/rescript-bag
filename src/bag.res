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
    let compare: (t, t) => int
  },
) => {
  module M = Map.Make(X)

  type elt = X.t

  @ocaml.doc(" invariant: multiplicities are all > 0 ")
  type t = M.t<int>

  let empty = M.empty

  let is_empty = M.is_empty

  let mem = M.mem

  let occ = (x, b) =>
    try M.find(x, b) catch {
    | Not_found => 0
    }

  let add = (x, ~mult=1, b) => {
    if mult < 0 {
      invalid_arg("add")
    }
    if mult == 0 {
      b
    } else {
      try {
        let m = M.find(x, b)
        M.add(x, m + mult, b)
      } catch {
      | Not_found => M.add(x, mult, b)
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
    M.update(x, f, b)
  }

  let singleton = x => M.add(x, 1, M.empty)

  let remove = (x, ~mult=1, b) => {
    if mult < 0 {
      invalid_arg("remove")
    }
    if mult == 0 {
      b
    } else {
      M.update(
        x,
        x =>
          switch x {
          | None | Some(1) => None
          | Some(m) if m <= mult => None
          | Some(m) => Some(m - mult)
          },
        b,
      )
    }
  }

  let remove_all = M.remove

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
    M.merge(f, b1, b2)
  }

  let cardinal = b => M.fold((_, m, c) => m + c, b, 0)

  let elements = M.bindings

  let min_elt = M.min_binding

  let min_elt_opt = M.min_binding_opt

  let max_elt = M.max_binding

  let max_elt_opt = M.max_binding_opt

  let choose = M.choose

  let choose_opt = M.choose_opt

  let union = (b1, b2) => M.merge((_, o1, o2) =>
      switch (o1, o2) {
      | (None, None) => None
      | (None, Some(m)) | (Some(m), None) => Some(m)
      | (Some(m1), Some(m2)) => Some(max(m1, m2))
      }
    , b1, b2)

  let sum = (b1, b2) => M.merge((_, o1, o2) =>
      switch (o1, o2) {
      | (None, None) => None
      | (None, Some(m)) | (Some(m), None) => Some(m)
      | (Some(m1), Some(m2)) => Some(m1 + m2)
      }
    , b1, b2)

  let inter = (b1, b2) => M.merge((_, o1, o2) =>
      switch (o1, o2) {
      | (None, None)
      | (None, Some(_))
      | (Some(_), None) =>
        None
      | (Some(m1), Some(m2)) => Some(min(m1, m2))
      }
    , b1, b2)

  let diff = (b1, b2) => M.merge((_, o1, o2) =>
      switch (o1, o2) {
      | (None, _) => None
      | (Some(m), None) => Some(m)
      | (Some(m1), Some(m2)) if m1 <= m2 => None
      | (Some(m1), Some(m2)) => Some(m1 - m2)
      }
    , b1, b2)

  let disjoint = (b1, b2) => M.for_all((x1, _) => !mem(x1, b2), b1)

  let included = (b1, b2) => M.for_all((x1, m1) => m1 <= occ(x1, b2), b1)

  let iter = M.iter

  let fold = M.fold

  let for_all = M.for_all

  let exists = M.exists

  let filter = M.filter

  let partition = M.partition

  let split = (x, b) => {
    let (l, m, r) = M.split(x, b)
    (
      l,
      switch m {
      | None => 0
      | Some(m) => m
      },
      r,
    )
  }

  let find_first = M.find_first

  let find_first_opt = M.find_first_opt

  let find_last = M.find_last

  let find_last_opt = M.find_last_opt

  let map = f => {
    let f = m => {
      let m = f(m)
      if m <= 0 {
        invalid_arg("map")
      }
      m
    }
    M.map(f)
  }

  let mapi = f => {
    let f = (x, m) => {
      let m = f(x, m)
      if m <= 0 {
        invalid_arg("mapi")
      }
      m
    }
    M.mapi(f)
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
        assert (q > 0)
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

  let compare = M.compare(Stdlib.compare)

  let equal = M.equal(\"==")

  let to_seq = M.to_seq

  let to_seq_from = M.to_seq_from

  let add_seq = (s, b) => Seq.fold_left((b, (x, mult)) => add(x, ~mult, b), b, s)

  let of_seq = s => add_seq(s, empty)

  let print = (print_elt, fmt, b) => {
    Format.fprintf(fmt, "{@[")
    let first = ref(true)
    iter((x, m) => {
      if !first.contents {
        Format.fprintf(fmt, ",")
      }
      first := false
      Format.fprintf(fmt, "@ %a:%d", print_elt, x, m)
    }, b)
    if !first.contents {
      Format.fprintf(fmt, " ")
    }
    Format.fprintf(fmt, "@]}")
  }
}
