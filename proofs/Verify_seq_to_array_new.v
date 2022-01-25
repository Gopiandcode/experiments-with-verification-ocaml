Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import Seq_to_array_old.

(** Lazy values: a lazy value of type [a] is represented at type [unit->'a].
    [Lazyval P f] asserts that [f] is a lazy value whose evaluation produces
    a value satisfying the (pure) predicate [P]. *)

Definition Lazyval A `{EA:Enc A} (P:A->Prop) (f:val) : Prop :=
  SPEC_PURE (f tt) POST (fun a => \[P a]). 

Definition LSeq_node A `{EA:Enc A} (LSeq: list A -> t_ A -> Prop) (L:list A) (s: node_ A) : Prop :=
 match L with
 | nil => s = Nil
 | x::L' => exists f', s = Cons x f' /\ LSeq L' f'
 end. 

Lemma LSeq_node_Nil : forall A (EA:Enc A) (LSeq: list A -> t_ A -> Prop),
  LSeq_node LSeq (@nil A) Nil.
Proof using. intros. simpl. auto. Qed.

Lemma LSeq_node_Cons : forall A (EA: Enc A) (LSeq: list A -> t_ A-> Prop) (x: A) (L': list A) (f: func),
  LSeq L' f ->
  LSeq_node LSeq (x::L') (Cons x f).
Proof using. introv Hf. simpl. exists* f. Qed.

Fixpoint LSeq A `{EA: Enc A} (L: list A) (f: t_ A) : Prop :=
  Lazyval (LSeq_node (@LSeq A EA) L) f.

Lemma LSeq_intro : forall A `{EA:Enc A} (L:list A) (f: t_ A),
  SPEC_PURE (f tt) POST (fun a => \[(LSeq_node (@LSeq A EA) L) a]) ->
  LSeq L f.
Proof using.
  (* Coq forces us to do a case analysis on L in order to unfold the fixpoint definition. *)
  intros. unfold LSeq, Lazyval. destruct L; simpl; xapplys* H.
Qed.

Lemma LSeq_if : forall A `{EA:Enc A} (L:list A) (f: t_ A),
    LSeq L f ->
    (SPEC_PURE (f tt) POST (fun a => \[(LSeq_node (@LSeq A EA) L) a])) .
Proof using.
  intros A EA L; case L as [| hd tl]; intros f; simpl; auto.
Qed.

Fixpoint itoa (m: int) (n: nat) :=
  match n with
  | O => nil
  | S n => m :: itoa (m + 1) n
  end.

Lemma itoa_pos : forall start nb,
  nb > 0 ->
  itoa start (Z.to_nat nb) = start :: itoa (start+1) (Z.to_nat (nb-1)).
Proof using.
  introv Hnb.
  case_eq (to_nat nb); try (intros H; math).
  intros n' Hnb'; simpl; apply f_equal.
  assert (n' = to_nat (nb - 1)) as H. { math. }
  rewrite H; auto.
Qed.

Lemma int_range_lspec : forall start nb,
   0 <= nb  ->
  SPEC_PURE (int_range start nb)
    POST (fun f => \[ LSeq (itoa start (Z.to_nat nb)) f ]).
Proof using.
  introv. gen start. induction_wf IH: (downto 0) nb; intros. xcf.
  xlet. xvals. apply LSeq_intro. xapp. clear Spec_f0__. xif;=> C.
  { xapp; try (hnf; math). intros s' HS'. xvals. rewrite itoa_pos; try math.
    applys_eq* LSeq_node_Cons. }
  { xvals. applys_eq LSeq_node_Nil. math_rewrite (nb = 0). auto. }
Qed.  

Lemma fold_spec : forall A `{Enc A} B `{Enc B} (ls: list A) f (init : B) s (fp: B -> A -> B),
    (forall acc v,
        SPEC_PURE (f acc v)
        POST \[= fp acc v]) ->
  SPEC (fold f init s)
    PRE \[LSeq ls s]
    POST \[= List.fold_left fp ls init].
Proof using.
  introv Hspec. gen s init. induction ls; xcf.
  { xpull ;=> HLseq. apply LSeq_if in HLseq. xapp. xmatch. xvals. auto. }
  { xpull ;=> HLseq. apply LSeq_if in HLseq. xapp ;=> nxt'. simpl LSeq_node;=>[nxt [-> Hnxt]].
    xmatch. xapp. xapp; auto. xsimpl. auto. }
Qed.

Lemma length_spec : forall A `{Enc A} (ls: list A) s,
  SPEC (length'__ s)
    PRE \[LSeq ls s]
    POST (fun len => \[ len = length ls ]).
Proof using.
  xcf; auto. xlet (fun f => forall (acc: int) (v: A), SPEC_PURE (f acc v) POST \[= (acc + 1) ]).
  { xval. xsimpl. math. }
  xpull ;=> Hs.
  xapp (@fold_spec _ _ _ _ ls f0__ 0 s (fun (acc: int) _ => acc + 1)); auto.
  xsimpl.
  clear.
  cut (forall a, List.fold_left (fun (acc : credits) (_ : A) => acc + 1) ls a = a + length ls). {
    intros H.
    apply H.
  }
  induction ls.
  - intros a; simpl; rewrite length_nil; auto; math.
  - intros a'; simpl. rewrite IHls. rewrite length_cons; math.
Qed.

Lemma iteri_spec : forall A `{EA: Enc A} (l: list A) (f: func) (s: t_ A),
  forall (I: list A -> hprop),
  (forall x t r i, (l = t++x::r) -> i = length (t) ->
     SPEC (f i x) PRE (I t) POSTUNIT (I (t&x))) ->  
  SPEC (iteri f s)
    PRE (\[@LSeq A EA l s] \* I nil)
    POSTUNIT (I l).
Proof using.
  =>> M. xcf; auto.
  xlet.
  asserts aux_spec: (
   forall i r t s,
     l = t ++ r ->
     i = length t ->
     SPEC (aux f s i)
     PRE (I t \* \[LSeq r s])
     POSTUNIT (I l)
                    ).
  {
    intro i; induction_wf IH: (upto (length l)) i.
    intros r t s' Hl Hi.
    eapply Spec_aux; clear Spec_aux.
    xpull ;=> HLseq. apply LSeq_if in HLseq.
    case_eq r.
    * intros ->. xapp. xmatch. xvals. rewrite app_nil_r in Hl; rewrite Hl; xsimpl.
    * intros x xs ->. xapp;=>result [nxt_r [-> Hnxt_r]].
      xmatch. xseq. xapp~ (M x t xs).
      xapp.
      ** unfold upto. split; try math.
         rewrite Hl; rewrite length_app; rewrite Hi; rewrite length_cons.
         math.
      ** rewrite Hl. rewrite <- app_cons_r. auto.
      ** rewrite length_last. math.
      ** auto.
      ** xsimpl.
  }
  xpull;=> Hlseq.
  xapp (aux_spec 0 l); auto; try xsimpl.
Qed.

Hint Extern 1 (RegisterSpec iteri) => Provide iteri_spec.

Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xpull ;=> HLseq; apply LSeq_if in HLseq.
  case_eq l.
  - intros ->; xapp; xmatch. xapp;=> x; xsimpl.
  - intros x xs Hl; rewrite Hl in *; xapp ;=> result [nxt_r [-> Hnxt_r]].
    xmatch.
    xapp length_spec. { apply LSeq_intro; auto. applys HLseq. }
    xapp. { math. } => arr data Hdata.
    xlet.
    xseq.
    xapp (@iteri_spec A EA l f0__ s (fun ls => arr ~> Array (ls ++ (make (length l - length ls) x)) )).
    * {
      intros y t ys i IHl IHi.
      xapp Spec_f0__; clear Spec_f0__.
      xapp.
      rewrite IHl; rewrite IHi.
      apply int_index_prove; try math.
      rewrite <- length_eq. rewrite !length_app. rewrite length_cons. rewrite length_make; try math.
      xsimpl.
      rewrite length_last. math_rewrite ((length l - (1 + length t)) = ((length l - length t) - 1)).
      rewrite (@update_app_r _  _ 0 _ _ _ y IHi); try math.
      rewrite app_last_l.
      apply f_equal.
      rewrite make_eq_cons_make_pred; try (rewrite IHl; rewrite length_app; rewrite length_cons; math).
      rewrite update_zero.
      auto.
    }
    * apply LSeq_intro; rewrite Hl; eapply HLseq.
    * rew_list; math_rewrite ((length l - 0) = length l); rewrite Hl; auto.
    * xvals. math_rewrite ((length l - length l) = 0); rewrite make_zero; rew_list; auto.
Qed.      
