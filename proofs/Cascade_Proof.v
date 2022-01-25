Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From Proofs Require Import Cascade_Spec.
From Proofs Require Import Cascade.

(* -------------------------------------------------------------------------- *)


(* -------------------------------------------------------------------------- *)

Theorem cons_spec A:
  forall I seqs,
  forall (x : A) c,
    SPEC (Cascade.cons x c)
    PRE  (\[@PureCascade A I seqs c])
    POST (fun c' => \[@PureCascade A I (List.cons x seqs) c']).
Proof.
  (* This is viewed by CFML as a partial application. *)
  intros.  xpartial. intros xc. xpull. intros [ ? Hxc ].
  (* There remains to prove that if [c] is a valid cascade
     and if [xc] is the result of the application [cons x c]
     then [xc] is a valid cascade. *)
  xunfold Cascade. xpull. intros S Hdup Hpermitted Hspec.
  (* This requires exhibiting the invariant of the new cascade,
     which must be built on top of the invariant [S] of the
     cascade [c]. Tricky. *)
  xsimpl (fun xs c' =>
    match xs with
    | nil =>
        \[ c' = xc ] \* S nil c
    | y :: ys =>
        \[ y = x ] \* S ys c'
    end
  ).
  { intros [ | y ys ] c'.
    { xpull. intros. subst c'.
      xdup (S nil c). (* TEMPORARY should not be necessary? *)
      xapply~ Hxc.
      xcf. xret.
      xsimpl~. subst. xsimpl~. }
    { xpull. intros. subst y.
      xapply~ Hspec. xsimpl~.
      intros [ | ]; intros; xsimpl~.
      { eauto. }
      { unfold append. xsimpl. (* weird *) }
    }
  }
  { intros [ | y ys ] c'; xpull; intros; subst.
    { xsimpl~. unfold cons. simpl. eauto. }
    { xchange~ Hpermitted. xpull. intros. xsimpl~. unfold cons. simpl. eauto. }
  }
  { intros [ | y ys ] c'; eauto with duplicable. }
  { eauto. }
Qed.
