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
    intros l0; induction l0 as [| h t Ht]; intros acc i0 Hi Hl.
    - {
        xapp Spec_aux.
        xmatch.
        xval.
        xsimpl.
        rewrite Hl; auto.
      }
    - {
        xapp Spec_aux.
        xmatch.
        - {
            xapp.
            xsimpl.
            destruct C0 as [C0 C1]; rewrite C0; apply istrue_isTrue_forw in C1; rewrite C1; rewrite Z2Nat.inj_0; auto.
          }
        - {
            assert (0 < i0)%Z. {
              case (C0 h t); try (intro Habs; contradiction Habs; auto).
              rewrite istrue_neg_isTrue; intro Hn0.
              apply (@Z.le_neq 0 i0);  split; auto.
            }
            xapp Ht; auto;
              try (rewrite rev_cons; rewrite app_last_l; auto);
              try (rewrite Z.sub_1_r; apply Zlt_0_le_0_pred; auto).
            xsimpl.
            rewrite Z.sub_1_r.
            rewrite Z2Nat.inj_pred.
            assert (0 < to_nat i0) as H1 by math.
            gen H1; case (to_nat i0); auto; math.
          }
      }
  }
  xif; first [math| idtac]; intro; xval.
  xapp Hacc; auto; xsimpl.
  simpl; rewrite rev_nil; rewrite app_nil_l; auto.
Qed.
