(**************************************************************************)
(*                                                                        *)
(*  ReML - an OCaml library for combinatorics                             *)
(*                                                                        *)
(*  Copyright (C) 2012                                                    *)
(*    Remy El Sibaie                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** Knuth's dancing links (aka DLX)
    see http://en.wikipedia.org/wiki/Dancing_Links *)

type t
  (** The internal data structure for DLX *)

val create: ?primary:int -> bool array array -> t
  (** Creates a DLX data structure from a matrix of Boolean values.
      The purpose of DLX is to solve the Exact Matrix Cover problem
      for this matrix, that is to find one (or all) subsets of rows
      such that each column contains exactly one value [true] for primary
      columns and at most one [true] value for secondary columns.

      If [primary] is given, it means that the first [primary] columns are
      primary; otherwise, all columns are primary columns. *)

val get_first_solution: t -> int list
  (** Returns the first solution that is found.
      Raises [Not_found] if the problem has no solution. *)

val count_solutions: t -> int
  (** Returns the number of solutions. *)

val get_solution_array: t -> int list array
  (** Returns all solutions, as an array of lists.
      Each solution is a list of row indices (rows are 0-based). *)

val get_solution_list: t -> int list list
  (** Returns all solutions, as a list of lists. *)

type solution

val iter_solution: (solution -> unit) -> t -> unit
  (** [iter_solution f p] applies [f] on each solution of the problem [p],
      one at a time *)

val list_of_solution: solution -> int list
  (** Decodes a solution as a list of rows (rows are 0-based) *)

val print_solution: Format.formatter -> solution -> unit
  (** Print a solution, as a space-separated list of integers *)
