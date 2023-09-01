Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import List_set_at_ind_new.

Fixpoint with_nth (A: Type) (i: nat) (x: A) (ls: list A) {struct ls} :=
  match ls with
  | nil => nil
  | h :: t =>
      match i with
      | O => x :: t
      | S n => h :: with_nth n x t
      end
  end.

Lemma set_at_idx_spec : forall A (i: int) (x: A) (l:list A),
    0 <= i ->
  SPEC (set_at_idx i x l)
    PRE \[]
    POST \[= with_nth (Z.to_nat i) x l].
Proof using.
  xcf.
  xlet.
  asserts Hacc : (forall (l0 acc: list A) (i0: int), 0 <= i0 ->
                          l = LibList.rev acc ++ l0 ->
                           SPEC (aux l0 acc i0)
                                PRE \[]
                                POST \[= (LibList.rev acc ++ with_nth (Z.to_nat i0) x l0)]).
  {
   admit.
  }

Admitted.
