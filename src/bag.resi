@@ocaml.text(/* ************************************************************************ */
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

" Bags (aka multisets).

    A bag is merely a map that binds each element to its multiplicity
    in the bag (see function [occ] below).

    All operations over bags are purely applicative (no side-effects).
    Bags are internally implemented with AVLs (from module [Map])
    and consequently operations such as [occ], [mem], [add], or [remove]
    take time logarithmic in the size (i.e. number of distinct elements)
    of the bag.

    Caveat: There is no unicity of representation. Consequently, the
    polymorphic equality [(=)] must not be used on bags. Functions
    [compare] and [equal] are provided to compare bags.

    Similarly, the polymorphic hash function [Hashtbl.hash] must not be
    used on bags. If one intends to use bags as hash table heys, a suitable
    hash function must be defined, with something like

    {[
      let hash b =
        fold (fun x n h -> 5003 * (5003 * h + hash x) + n) b 0
    ]}

    where [hash] is a suitable hash function for the bag elements.
")

module Make: (
  X: {
    type t

    @ocaml.doc(" Bags are implemented using [Map.Make] and therefore require elements
      to be comparable. ")
    let compare: (t, t) => int
  },
) =>
{
  type elt = X.t

  @ocaml.doc(" The immutable type of bags. ")
  type t

  @ocaml.doc(" The empty bag. ")
  let empty: t

  @ocaml.doc(" Test for emptiness. ")
  let is_empty: t => bool

  @ocaml.doc(" [occ x b] is the number of occurrences of [x] in bag [b].
      It returns 0 when [x] is not in [b]. ")
  let occ: (elt, t) => int

  @ocaml.doc(" [mem x b] checks whether [x] belongs to [b], i.e. has a multiplicity
      greater than 0. ")
  let mem: (elt, t) => bool

  @ocaml.doc(" [add x ?mult b] returns a new bag where the multiplicity of [x]
      is increased by [mult] (defaults to one).
      Raises [Invalid_argument] if [mult] is negative.")
  let add: (elt, ~mult: int=?, t) => t

  @ocaml.doc(" [update x f b] returns a bag containing the same elements as
      [b], except for element [x] whose multiplicity is [f (occ x b)].
      Raises [Invalid_argument] if [f] returns a negative value. ")
  let update: (elt, int => int, t) => t

  @ocaml.doc(" [singleton x] is a bag with one element [x], with multiplicity [1]. ")
  let singleton: elt => t

  @ocaml.doc(" [remove x ?mult b] returns a new bag where the multiplicity of [x]
      is decreased by [mult] (defaults to one).
      Raises [Invalid_argument] if [mult] is negative.")
  let remove: (elt, ~mult: int=?, t) => t

  @ocaml.doc(" [remove_all x b] returns a new bag where the element [x] is removed. ")
  let remove_all: (elt, t) => t

  @ocaml.doc(" [merge f b1 b2] computes a bag whose elements are a subset of
      the elements of [b1] and of [b2]. The presence of each such
      element, and the corresponding multiplicity, is determined with
      the function [f].  In terms of the [occ] operation, we have [occ
      x (merge f b1 b2) = f x (occ x b1) (occ x b2)] for any element
      [x], provided that [f x 0 0 = 0].
      Raises [Invalid_argument] if [f] returns a negative value. ")
  let merge: ((elt, int, int) => int, t, t) => t

  @ocaml.doc(" [cardinal b] is the sum of the multiplicities. ")
  let cardinal: t => int

  @ocaml.doc(" Returns the list of all elements of the given bag. Each element
     is given with its multiplicity. The returned list is sorted in
     increasing order of elements with respect to the ordering over
     the type of the elements. ")
  let elements: t => list<(elt, int)>

  @ocaml.doc(" Returns the smallest element in the given bag (with respect
      to the ordering) with its multiplicity,
      or raises [Not_found] if the bag is empty. ")
  let min_elt: t => (elt, int)

  @ocaml.doc(" Returns the smallest element of the given bag
      (with respect to the ordering) with its multiplicity,
      or [None] if the bag is empty. ")
  let min_elt_opt: t => option<(elt, int)>

  @ocaml.doc(" Returns the largest element in the given bag (with respect to
      the ordering) with its multiplicity, or raises [Not_found] if the
      bag is empty. ")
  let max_elt: t => (elt, int)

  @ocaml.doc(" Returns the largest element of the given bag (with respect to
      the ordering) with its multiplicity, or [None] if the bag is
      empty. ")
  let max_elt_opt: t => option<(elt, int)>

  @ocaml.doc(" Returns one element of the given bag with its multiplicity, or
      raises [Not_found] if the bag is empty. Which binding is chosen
      is unspecified, but equal elements will be chosen for equal
      bags. ")
  let choose: t => (elt, int)

  @ocaml.doc(" Returns one element of the given bag, or [None] if
      the set is empty. Which element is chosen is unspecified,
      but equal elements will be chosen for equal bags. ")
  let choose_opt: t => option<(elt, int)>

  @ocaml.doc(" [union b1 b2] returns a new bag [b] where, for all element x,
      [occ x b = max (occ x b1) (occ x b2)]. ")
  let union: (t, t) => t

  @ocaml.doc(" [sum b1 b2] returns a new bag [b] where, for all element x,
      [occ x b = occ x b1 + occ x b2]. ")
  let sum: (t, t) => t

  @ocaml.doc(" [mul b n] returns a new bag [b'] where, for all element x,
      [occ x b' = occ x b * n].
      Raises [Invalid_argument] if [n] is negative. ")
  let mul: (t, int) => t

  @ocaml.doc(" [div b1 b2] returns a pair [q, r] such that
      [b1 = sum (mul b2 q) r] and [q >= 0] is maximal. ")
  let div: (t, t) => (int, t)

  @ocaml.doc(" [divi b n] returns a pair [q, r] such that
      [b = sum (mul q n) r] and multiplicities in [r] are smaller than [n].
      Raises [Invalid_argument] is [n] is nonpositive. ")
  let divi: (t, int) => (t, t)

  @ocaml.doc(" [inter b1 b2] returns a new bag [b] where, for all element x,
      [occ x b = min (occ x b1) (occ x b2)]. ")
  let inter: (t, t) => t

  @ocaml.doc(" [diff b1 b2] returns a new bag [b] where, for all element x,
      [occ x b = max 0 (occ x b1 - occ x b2)]. ")
  let diff: (t, t) => t

  @ocaml.doc(" Test if two bags are disjoint. ")
  let disjoint: (t, t) => bool

  @ocaml.doc(" [included b1 b2] returns true if and only if, for all element x,
      [occ x b1 <= occ x b2]. ")
  let included: (t, t) => bool

  @ocaml.doc(" [iter f b] applies [f] to all elements in bag [b].  [f] receives the
      element as first argument, and its multiplicity as second argument.
      The elements are  passed to [f] in increasing order with respect to
      the ordering over the type of the elements. ")
  let iter: ((elt, int) => unit, t) => unit

  @ocaml.doc(" [fold f b a] computes [(f xN mN ... (f x1 m1 a)...)] , where [x1 ... xN]
      are the elements in bag [b] (in increasing order), and [m1 ... mN] are
      their multiplicities. ")
  let fold: ((elt, int, 'a) => 'a, t, 'a) => 'a

  @ocaml.doc(" [for_all p b] checks if all the elements of the bag satisfy the predicate
      [p]. ")
  let for_all: ((elt, int) => bool, t) => bool

  @ocaml.doc(" [exists p b] checks if at least one element of the bag satisfies the
      predicate [p]. ")
  let exists: ((elt, int) => bool, t) => bool

  @ocaml.doc(" [filter p b] returns the bag with all the elements in [b] that satisfy
       predicate [p]. Multiplicities are unchanged. ")
  let filter: ((elt, int) => bool, t) => t

  @ocaml.doc(" [partition p b] returns a pair of bags [(b1, b2)], where
      [b1] contains all the elements of [b] that satisfy the
      predicate [p], and [b2] is the bag with all the elements of
      [b] that do not satisfy [p]. ")
  let partition: ((elt, int) => bool, t) => (t, t)

  @ocaml.doc(" [split x b] returns a triple [(l, m, r)], where
        [l] is the bag with all the elements of [b] that
      are strictly less than [x];
        [r] is the bag with all the elements of [b] that
      are strictly greater than [x];
        [m] is the multiplicity of [x] in [b]. ")
  let split: (elt, t) => (t, int, t)

  @ocaml.doc(" [find_first f b], where [f] is a monotonically increasing function,
     returns the lowest element [x] of [b] such that [f x],
     or raises [Not_found] if no such key exists. ")
  let find_first: (elt => bool, t) => (elt, int)

  @ocaml.doc(" [find_first_opt f b], where [f] is a monotonically increasing function,
     returns an option containing the lowest element [x] of [b]
     such that [f x], or [None] if no such key exists. ")
  let find_first_opt: (elt => bool, t) => option<(elt, int)>

  @ocaml.doc(" [find_last f b], where [f] is a monotonically decreasing function,
     returns the largest element [x] of [b] such that [f x],
     or raises [Not_found] if no such key exists. ")
  let find_last: (elt => bool, t) => (elt, int)

  @ocaml.doc(" [find_last_opt f b], where [f] is a monotonically decreasing function,
     returns an option containing the largest element [x] of [m]
     such that [f x], or [None] if no such key exists. ")
  let find_last_opt: (elt => bool, t) => option<(elt, int)>

  @ocaml.doc(" [map f b] returns a bag with same elements as [b], where the
      multiplicity [m] of each element of [b] has been
      updated by the result of the application of [f] to [m].
      The elements are passed to [f] in increasing order
      with respect to the ordering over the type of the elements.
      Raises [Invalid_argument] if [f] returns a nonpositive value. ")
  let map: (int => int, t) => t

  @ocaml.doc(" Same as {!Bag.map}, but the function receives as arguments both the
      element and the associated multiplicity.
      Raises [Invalid_argument] if [f] returns a nonpositive value. ")
  let mapi: ((elt, int) => int, t) => t

  @ocaml.doc(" Total ordering between bags. ")
  let compare: (t, t) => int

  @ocaml.doc(" [equal b1 b2] tests whether the bags [b1] and [b2] are equal, that is,
      contain equal elements with equal multiplicities. ")
  let equal: (t, t) => bool

  @@ocaml.text(" {1 Iterators} ")

  @ocaml.doc(" Iterates on the whole bag, in ascending order of elements. ")
  let to_seq: t => Seq.t<(elt, int)>

  @ocaml.doc(" [to_seq_from x b] iterates on a subset of [b],
      in ascending order of elements, from element [x] or above. ")
  let to_seq_from: (elt, t) => Seq.t<(elt, int)>

  @ocaml.doc(" Adds the given elements to the bag, in order.
      Raises [Invalid_argument] if a multiplicity is negative. ")
  let add_seq: (Seq.t<(elt, int)>, t) => t

  @ocaml.doc(" Builds a bag from the given elements and multiplicities.
      Raises [Invalid_argument] if a multiplicity is negative. ")
  let of_seq: Seq.t<(elt, int)> => t

  let print: ((Format.formatter, X.t) => unit, Format.formatter, t) => unit
}
