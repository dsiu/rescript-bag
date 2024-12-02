/* ************************************************************************ */
/*  */
/* OCaml */
/*  */
/* Gabriel Scherer, projet Parsifal, INRIA Saclay */
/*  */
/* Copyright 2019 Institut National de Recherche en Informatique et */
/* en Automatique. */
/*  */
/* All rights reserved.  This file is distributed under the terms of */
/* the GNU Lesser General Public License version 2.1, with the */
/* special exception on linking described in the file LICENSE. */
/*  */
/* ************************************************************************ */

type t<'a, 'b> = Left('a) | Right('b)

let left = v => Left(v)
let right = v => Right(v)

let is_left = x =>
  switch x {
  | Left(_) => true
  | Right(_) => false
  }

let is_right = x =>
  switch x {
  | Left(_) => false
  | Right(_) => true
  }

let find_left = x =>
  switch x {
  | Left(v) => Some(v)
  | Right(_) => None
  }

let find_right = x =>
  switch x {
  | Left(_) => None
  | Right(v) => Some(v)
  }

let map_left = (f, x) =>
  switch x {
  | Left(v) => Left(f(v))
  | Right(_) as e => e
  }

let map_right = (f, x) =>
  switch x {
  | Left(_) as e => e
  | Right(v) => Right(f(v))
  }

let map = (~left, ~right, x) =>
  switch x {
  | Left(v) => Left(left(v))
  | Right(v) => Right(right(v))
  }

let fold = (~left, ~right, x) =>
  switch x {
  | Left(v) => left(v)
  | Right(v) => right(v)
  }

let iter = fold

let for_all = fold

let equal = (~left, ~right, e1, e2) =>
  switch (e1, e2) {
  | (Left(v1), Left(v2)) => left(v1, v2)
  | (Right(v1), Right(v2)) => right(v1, v2)
  | (Left(_), Right(_)) | (Right(_), Left(_)) => false
  }

let compare = (~left, ~right, e1, e2) =>
  switch (e1, e2) {
  | (Left(v1), Left(v2)) => left(v1, v2)
  | (Right(v1), Right(v2)) => right(v1, v2)
  | (Left(_), Right(_)) => -1
  | (Right(_), Left(_)) => 1
  }
