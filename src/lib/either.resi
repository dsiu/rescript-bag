@@ocaml.text(/* ************************************************************************ */
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

" Either type.

    Either is the simplest and most generic sum/variant type:
    a value of [('a, 'b) Either.t] is either a [Left (v : 'a)]
    or a [Right (v : 'b)].

    It is a natural choice in the API of generic functions where values
    could fall in two different cases, possibly at different types,
    without assigning a specific meaning to what each case should be.

    For example:

{[List.partition_map:
    ('a -> ('b, 'c) Either.t) -> 'a list -> 'b list * 'c list]}

    If you are looking for a parametrized type where
    one alternative means success and the other means failure,
    you should use the more specific type {!Result.t}.

    @since 4.12
")

/* Unlike [result], no [either] type is made available in Stdlib,
   one needs to access [Either.t] explicitly:

   - This type is less common in typical OCaml codebases,
     which prefer domain-specific variant types whose constructors
     carry more meaning.
   - Adding this to Stdlib would raise warnings in existing codebases
     that already use a constructor named Left or Right:
     + when opening a module that exports such a name,
       warning 45 is raised
     + adding a second constructor of the same name in scope kicks
       in the disambiguation mechanisms, and warning 41 may now
       be raised by existing code.

   If the use becomes more common in the future we can always
   revisit this choice.
*/

@ocaml.doc(" A value of [('a, 'b) Either.t] contains
    either a value of ['a]  or a value of ['b] ")
type t<'a, 'b> = Left('a) | Right('b)

@ocaml.doc(" [left v] is [Left v]. ")
let left: 'a => t<'a, 'b>

@ocaml.doc(" [right v] is [Right v]. ")
let right: 'b => t<'a, 'b>

@ocaml.doc(" [is_left (Left v)] is [true], [is_left (Right v)] is [false]. ")
let is_left: t<'a, 'b> => bool

@ocaml.doc(" [is_right (Left v)] is [false], [is_right (Right v)] is [true]. ")
let is_right: t<'a, 'b> => bool

@ocaml.doc(" [find_left (Left v)] is [Some v], [find_left (Right _)] is [None] ")
let find_left: t<'a, 'b> => option<'a>

@ocaml.doc(" [find_right (Right v)] is [Some v], [find_right (Left _)] is [None] ")
let find_right: t<'a, 'b> => option<'b>

@ocaml.doc(" [map_left f e] is [Left (f v)] if [e] is [Left v]
    and [e] if [e] is [Right _]. ")
let map_left: ('a1 => 'a2, t<'a1, 'b>) => t<'a2, 'b>

@ocaml.doc(" [map_right f e] is [Right (f v)] if [e] is [Right v]
    and [e] if [e] is [Left _]. ")
let map_right: ('b1 => 'b2, t<'a, 'b1>) => t<'a, 'b2>

@ocaml.doc(" [map ~left ~right (Left v)] is [Left (left v)],
    [map ~left ~right (Right v)] is [Right (right v)]. ")
let map: (~left: 'a1 => 'a2, ~right: 'b1 => 'b2, t<'a1, 'b1>) => t<'a2, 'b2>

@ocaml.doc(" [fold ~left ~right (Left v)] is [left v], and
    [fold ~left ~right (Right v)] is [right v]. ")
let fold: (~left: 'a => 'c, ~right: 'b => 'c, t<'a, 'b>) => 'c

@ocaml.doc(" [iter ~left ~right (Left v)] is [left v], and
    [iter ~left ~right (Right v)] is [right v]. ")
let iter: (~left: 'a => unit, ~right: 'b => unit, t<'a, 'b>) => unit

@ocaml.doc(" [for_all ~left ~right (Left v)] is [left v], and
    [for_all ~left ~right (Right v)] is [right v]. ")
let for_all: (~left: 'a => bool, ~right: 'b => bool, t<'a, 'b>) => bool

@ocaml.doc(" [equal ~left ~right e0 e1] tests equality of [e0] and [e1] using [left]
    and [right] to respectively compare values wrapped by [Left _] and
    [Right _]. ")
let equal: (~left: ('a, 'a) => bool, ~right: ('b, 'b) => bool, t<'a, 'b>, t<'a, 'b>) => bool

@ocaml.doc(" [compare ~left ~right e0 e1] totally orders [e0] and [e1] using [left] and
    [right] to respectively compare values wrapped by [Left _ ] and [Right _].
    [Left _] values are smaller than [Right _] values. ")
let compare: (~left: ('a, 'a) => int, ~right: ('b, 'b) => int, t<'a, 'b>, t<'a, 'b>) => int
