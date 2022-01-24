Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import Seq_to_array_old.

Check (fun h nxt => Cons h nxt).


Fixpoint MSeq A `{EA: Enc A} (ls: list A) (f: val) : hprop :=
  match ls with
  | nil => \[ SPEC (f val_unit) PRE \[]  POST \[= (Nil: node_ A) ] ]
  | h :: t =>
      \exists nxt,
          \[ SPEC (f val_unit) PRE \[] POST \[= Cons h nxt]] \*
           @MSeq A EA t nxt
  end.

Fixpoint itoa (m: nat) (n: nat) :=
  match n with
  | O => nil
  | S n => Z.of_nat m :: itoa (S m) n
  end.

Lemma int_range_spec : forall m n,
   0 <= m -> 0 <= n  ->
  SPEC (int_range m n)
    PRE \[]
    POST (fun f => MSeq (itoa (Z.to_nat m) (Z.to_nat n)) f).
Proof using.
  intros m n Hm Hn; gen Hm Hn.
  induction_wf IH: (downto 0) n.
  intros Hm Hn.
  xcf.
  xlet.
  xval.
  case_eq (Z.to_nat n). 
  - intros Heq. simpl MSeq.
    xsimpl.
    applys~ Spec_f0__.
    Unshelve. exact tt.
    xif; intro Hcond; try math.
    xval.
    xsimpl.
    auto.
  - intros n' Hn'; simpl MSeq.
Admitted.    
  
