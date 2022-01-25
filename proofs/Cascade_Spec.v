Set Implicit Arguments.
From TLC Require Import LibTactics LibListZ LibInt.
From CFML Require Import WPLib Stdlib.
(* From CFML Require Import CFHeaps CFApp CFPrint CFTactics CFDuplicable. *)
(* Require Import LibSeq. *)
Require Import Cascade.

(* -------------------------------------------------------------------------- *)

(* The specification of a cascade. *)

Section Cascade.

(* The type of the elements that we wish to enumerate. *)

Variable A : Type.

(* The cascade invariant. *)

(* For now, we restrict our attention to a cascade without mutable internal
   state, which therefore is duplicable. A cascade may still access a piece of
   external mutable state, described by an assertion [I] that is supplied from
   the outside when the cascade is queried. We require [I] to be invariant;
   this means that several cascades on the same state [I] may exist (and be
   used) at the same time. One could also imagine a scenario where [I] is
   parameterized over the sequence [xs] of elements produced so far, but this
   sounds less useful, since in that case only one cascade would be useable. *)

Variable I : hprop.

(* The predicates [permitted seqs] and [complete seqs] describe the sequences
   of elements that may be produced by this cascade. See [LibSeq]. *)

Variable seqs : list A.

(* The predicate [c ~> Cascade xs] means that [c] is a valid cascade, which has
   already produced the elements [xs]. *)

(* This predicate is recursive: indeed, when [c] is queried, it returns a pair
   of an element [x] and a new cascade which has already produced [xs & x].
   Furthermore, in general, a cascade could be infinite, so this predicate is
   co-inductive.

   Instead of using Coq's native co-inductive predicates, we use an
   impredicative encoding. We require an internal description of the cascade,
   that is, a predicate [S] parameterized by [xs] and [c], such that [S] holds
   now and [S] is preserved when the cascade is queried. One can think of [S]
   as a simulation, that is, a witness that we are inside the greatest fixed
   point. Because we wish to restrict our attention to duplicable cascades, we
   require [S] to be duplicable. We still allow [S] to inhabit [hprop], as
   opposed to [Prop], because we have thunks in mind.

   We note that, when [Cascade xs c] holds, then [Cascade] itself is a valid
   witness for [S]. (This is proved below.) So, [Cascade] really is the
   greatest predicate that satisfies these conditions. *)

(* The above definition can be simplified in the case where [S] is pure. *)
Definition PureCascade (xs : list A) (c : func) : Prop :=
  exists (S : list A -> func -> Prop),
  S xs c /\
  (
    forall xs c,
    S xs c ->
    SPEC (c tt)
      INV  I
      POST (fun o => \[
        match o with
        | Nil => xs = List.nil
        | Cons x c => S (xs & x) c
        end])
  ).

(* -------------------------------------------------------------------------- *)

(* This simplified definition helps construct a cascade in the case
   where [S] is pure. See also the tactic [pure_cascade] further on. *)

End Cascade.
