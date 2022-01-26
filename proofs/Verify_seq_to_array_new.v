Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import Seq_to_array_new.

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

Lemma list_fold_spec : forall A `{EA: Enc A} B `{EB: Enc B}
                              (f: func) (init: B) (l: list A),
  forall (I: list A -> B -> hprop),
  (forall acc v t r, (l = t++v::r) ->
     SPEC (f acc v)
     PRE (I t acc)
     POST (fun acc => I (t&v) acc)) ->
  SPEC (List_ml.fold_left f init l)
    PRE (I nil init)
    POST (fun acc => I l acc).
Proof using.
  intros A EA B EB f init l I f_spec. gen init.
  cuts G: (forall r t init,
              l = t ++ r ->
              SPEC (List_ml.fold_left f init r)
              PRE I t init
              POST (fun acc : B => I l acc)).
  { intros init; applys~ (G l nil init). }
  intros r. induction_wf IH: list_sub r.
  intros t init Ht. xcf.
  xmatch.
  - xvals.
    rewrite Ht. rewrite <- TEMP; rew_list; xsimpl.
  - xapp (f_spec init a t l1); auto. { rewrite Ht. rewrite TEMP. auto. }
    intros acc.
    xapp. rewrite <- TEMP. apply list_sub_cons. { rew_list; try rewrite TEMP; auto. }
    xsimpl.
Qed.

Lemma list_fold_length_rev : forall A (xs : list A), 
    List.fold_left
         (fun (pair0 : credits * list A) (x : A) =>
            let (i, acc) := pair0 in (i + 1, x :: acc)) xs (0, nil) =
      (length xs, rev xs).
Proof.
  intros A.
  cuts G: (forall (xs : list A)  (i: int) (init: list A),
          List.fold_left
            (fun (pair0 : credits * list A) (x : A) =>
               let (i, acc) := pair0 in (i + 1, x :: acc))
            xs (i, init) = (i + length xs, rev xs ++ init)). {
    intros xs; rewrite G. f_equal; rew_list; auto.
  }
  intros xs; induction xs as [| x xs IHxs]; simpl.
  - intros i init; rew_list; f_equal; auto; math.
  - intros i init; simpl.
    rewrite IHxs.
    rewrite !length_cons.
    f_equal; try math. rew_list; auto.
Qed.

Lemma drop_last: forall A (xs rst: list A) (lst: A),
    rev xs = lst :: rst ->
    drop (length xs - 1) xs = lst :: nil.
Proof.
  intros A xs. induction_wf IH: list_sub xs.
  case_eq xs.
  - intros Hxs rst lst; rewrite rev_nil; intros H; inversion H.
  - intros hd tl Hxs; intros rst lst Hlst; rewrite length_cons.
    math_rewrite ((1 + length tl - 1) = length tl).
    case_eq tl.
    * intros Htl. rewrite Htl in *. rewrite rev_cons in Hlst.
      rewrite last_nil in Hlst.
      rewrite length_nil; rewrite drop_zero.
      f_equal. inversion Hlst; auto.
    * intros y ys Hys; rewrite length_cons.
      math_rewrite (1 + length ys = length ys + 1).
      rewrite drop_cons; try math.
      asserts Hlen: ((length ys) = length (y :: ys) - 1). {
        rewrite length_cons; math.
      } rewrite Hlen; clear Hlen.
      rewrite <- Hys.
      rewrite rev_cons in Hlst.
      rewrite <- (app_cons_one_r lst) in Hlst.
      assert (lst :: nil = nil & lst) by  (rew_list; auto).
      rewrite H in Hlst.
      assert (Hlst' := Hlst).
      apply last_eq_middle_inv in Hlst.
      case Hlst; clear Hlst.
      ** intros [Htl [Hlsthd Hrd] ].
         (* B109 *)
         apply rev_eq_nil_inv in Htl.
         rewrite Htl in Hys; inversion Hys.
      ** intros [rst_but_last Hrst].
         eapply (IH tl _ rst_but_last lst).
         rewrite Hrst in Hlst'.
         rewrite <- last_app in Hlst'.
         apply last_eq_last_inv in Hlst'.
         case Hlst' as [H1 H2].
         rewrite H1.
         rewrite app_last_l.
         rewrite app_nil_l.
         auto.
         Unshelve.
         rewrite Hxs. apply list_sub_cons.
Qed.    

Lemma drop_nth : forall A l v r i (xs: list A),
    xs = l ++ v :: r ->
    i = length l ->
    drop i xs = v :: drop (i + 1) xs.
Proof.
  intros A l v r i xs -> ->.
  rewrite drop_app_length.
  rewrite app_cons_r.
  assert ((length l + 1) = length (l & v)) as H by (rewrite length_last; math).
  rewrite H.
  rewrite drop_app_length.
  auto.
Qed.

Lemma case_rev_split : forall A (xs: list A) v l r,
    rev xs = l ++ v :: r ->
    xs = rev r ++ v :: rev l.
Proof.
  intros A xs; induction xs.
  - intros v l r; rewrite rev_nil; intros Hnil.
    apply nil_eq_app_inv in Hnil. case Hnil as [H1 H2].
    inversion H2.
  - intros v l r. 
    intros Hr; assert (Hr' := Hr).
    rewrite rev_cons in Hr. rewrite (app_cons_r v) in Hr.
    apply last_eq_middle_inv in Hr.
    case Hr.
    * intros [Hrevls [Ha Hnil]].
      rewrite Hnil. rewrite rev_nil.
      rewrite app_nil_l. rewrite Ha.
      apply f_equal.
      rewrite <- Hrevls.
      rewrite rev_rev.
      auto.
    * intros [pre Hrpre].
      rewrite Hrpre in Hr'.
      rewrite rev_cons in Hr'.
      rewrite <- last_cons in Hr'.
      rewrite <- last_app in Hr'.
      apply last_eq_last_inv in Hr'.
      case Hr' as [H1 H2].
      rewrite (IHxs _ _ _ H1).
      rewrite Hrpre.
      rewrite rev_last.
      rew_list.
      auto.
Qed.      

Lemma to_array_spec : forall A `{EA:Enc A} (l:list A) (s:func),
  SPEC (to_array s)
    PRE (\[LSeq l s])
    POST (fun a => a ~> Array l).
Proof using.
  xcf.
  xlet (fun (f: func) =>
     forall (i: int) (acc: list A) (x: A),
       SPEC_PURE (f (i,acc) x)
                 POST \[= (i + 1, x :: acc)]).
  { xmatch. xvals. auto. } 
  xpull ;=> HLseq; apply LSeq_if in HLseq.
  xapp (@fold_spec _ _ _ _ l f0__ (0, nil) s
                   (fun (pair: int * list A) (x: A) =>
                      let (i, acc) := pair in
                      (i + 1, x :: acc))); auto.
  { intros [i acc] x. xapp. xsimpl. auto. }
  { apply LSeq_intro; auto. }
  clear Spec_f0__.
  xmatch. 
  rewrite list_fold_length_rev in H0.
  inversion H0 as [Hlen].
  case_eq l.
  - intros ->. xmatch. xapp;=> x; xsimpl.
  - intros x xs Hl; rewrite Hl in *.
    xmatch. { apply nil_eq_rev_inv in H2. inversion H2. }
    xapp. { math. } => arr data Hdata.
    xlet.
    xlet.
    xapp (@list_fold_spec A EA int _ f1__ idx rest (fun t i =>
        \[i = length l - length t - 2] \*
        arr ~> Array ((make (i + 1) init) ++ 
                                 drop (i + 1) l)
         )).
    * {
        introv Hrst. apply Spec_f1__; clear Spec_f1__.
        assert (length (init :: rest) = length l) as Htmp by
                (rewrite H2; rewrite length_rev; rewrite Hl; auto).
        rewrite length_cons in Htmp.
        rewrite Hrst in Htmp; rewrite length_app in Htmp.
        rewrite length_cons in Htmp.
        xpull ;=> Hacc.
        xseq.
        xapp. {
            apply int_index_prove; try math.
            rewrite Hacc.
            rewrite <- length_eq.  rewrite length_app.
            rewrite length_make; try math.
        }
        xvals.
        {
          rewrite Hacc. rewrite <- Htmp.
          rewrite length_last. math.
        }
        rewrite update_app_l; try (rewrite length_make; math).        
        rewrite make_succ_r; try math.
        rewrite (@update_middle _ acc (make acc init) nil v init);
          try (rewrite length_make; math).
        rewrite app_nil_r.
        math_rewrite ((acc - 1 + 1) = acc).
        rewrite app_last_l.
        cut (v :: drop (acc + 1) l = drop acc l). {
          intros ->; auto.
        }
        rewrite Hl.
        rewrite Hrst in H2.
        rewrite <- app_cons_l in H2.
        symmetry in  H2.
        pose proof (case_rev_split (x :: xs) v (init :: t) r H2) as H1.
        rewrite H1.
        assert (length (rev r) = acc) as Hr by (rewrite length_rev; math).
        assert (length (rev r & v) = acc + 1) as Hrev by
          (rewrite length_last; rewrite length_rev; math).
        rewrite  app_cons_r at 1; rewrite <- Hrev at 1.
        rewrite <- Hr at 1.
        rewrite !drop_app_length.
        auto.
      }
    * rewrite Pidx. rewrite Hl. rewrite length_cons. rewrite length_nil. math.
    * {
        rewrite Hl; rewrite Pidx; rewrite !length_cons.
        math_rewrite ((1 + length xs - 2 + 1) = length xs).
        assert (length xs = length (x :: xs) - 1) as H' by (rewrite length_cons; math).
        rewrite H' at 2. symmetry in H2. rewrite (drop_last (x :: xs) H2).
        rewrite <- make_succ_r; try math.
        rewrite Hdata. rewrite length_cons.
        math_rewrite (1 + length xs = length xs + 1); auto.
      }
    * {
        intros i Hi. xmatch. xvals.
        rewrite Hi.
        assert (length (init :: rest) = length l) as Htmp by
            (rewrite H2; rewrite length_rev; rewrite Hl; auto).
        rewrite length_cons in Htmp.
        assert (length rest = length l - 1) as Hrest by math.
        clear Htmp. rewrite Hrest.
        math_rewrite
          ((length l - (length l - 1) - 2 + 1) = 0).
        rewrite make_zero; rewrite drop_zero.
        rewrite app_nil_l.
        auto.
      }
Qed.
