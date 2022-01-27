Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A IA.

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import Vector_filter_new.

Lemma filter_eq: forall A (f: A -> bool) l,
    filter f l = List.filter f l.
Proof.
  intros A f l; induction l.
  - simpl; rewrite filter_nil; auto.
  - simpl; rewrite filter_cons.
    rewrite If_istrue; case_eq (f a); simpl; intros Hfa;
    rewrite IHl; auto.
Qed.

Lemma drop_cons_unfold : forall A `{IA: Inhab A} (l: list A) i,
    0 <= i < length l ->
    drop i l = l[i] :: drop (i + 1) l.
Proof.
  intros A IA l; induction l.
  - intros i; rewrite length_nil; math.
  - intros i [Hgt Hlt].
    case (Zle_lt_or_eq _ _ Hgt).
    * intros Hgt1; rewrite length_cons in Hlt.
      math_rewrite (i = (i - 1) + 1).
      rewrite ! drop_cons; try math.
      rewrite IHl; try (split; math).
      rewrite read_cons_pos; try math.
      math_rewrite (i - 1 + 1 - 1 = i - 1).
      auto.
    * intros H; rewrite <- H.
      rewrite drop_cons; try math.
      rewrite !drop_zero.
      rewrite read_zero.
      auto.
Qed.

Lemma take_last_unfold : forall A `{IA: Inhab A} (l: list A) i,
    0 < i <= length l ->
    take i l = take (i - 1) l & l[i - 1].
Proof.
  intros A IA l; induction l.
  - intros i; rewrite length_nil; math.
  - intros i [Hgt Hlt].
    rewrite length_cons in Hlt.
    math_rewrite (i = (i - 1) + 1).
    rewrite ! take_cons; try math.
    math_rewrite (i - 1 + 1 = i).
    assert (i - 1 >= 0) as Hgtpri by math.
    case (Zle_lt_or_eq _ _ Hgtpri).
    * intros Hgt0.
      rewrite IHl; try math.
      rewrite take_cons_pos; try math.
      rewrite read_cons_pos; try math.
      rewrite last_cons; auto.
    * intros Hz0; rewrite <- Hz0.
      rewrite !take_zero. rewrite read_zero; rewrite last_nil.
      auto.
Qed.

Lemma length_filter_take_leq_base : forall A (f: A -> bool) (l: list A) iv,
    0 <= iv ->
    length (filter f (take iv l)) <= iv.
Proof.
  intros.
  case_eq (Z.le_ge_cases iv (length l)); intros Hcmp _; try math.
  - assert (iv = length (take iv l)) as Hlt by (rewrite length_take; try math).
    rewrite Hlt at 2; apply length_filter.
  - apply (Z.le_trans _ (length l) _); try math.
    rewrite take_ge; try math.
    apply length_filter.
Qed.

Lemma length_filter_take_leq : forall A (f: A -> bool) (l: list A) iv, 
    length (filter f (take iv l)) <= length (filter f l).
Proof.
  intros A f l; induction l.
  - intros iv; rewrite take_nil; rewrite filter_nil; math.
  - intros iv; case_eq (Z.le_gt_cases 0 iv).
    * intros Hlv _; case_eq (Zle_lt_or_eq _ _ Hlv).
      ** intros Hpos _.
         rewrite take_cons_pos; try math.
         rewrite !filter_cons.
         rewrite !If_istrue.
         pose proof (IHl (iv - 1)) as IHli.
         case (f a); simpl; try rewrite ! length_cons; try math.
      ** intros H0 _; rewrite <- H0. rewrite take_zero; rewrite filter_nil;
           rewrite length_nil; try math.
    * intros Hneg _; rewrite take_neg; try math; rewrite filter_nil;
        rewrite length_nil; try math.
Qed.      

Lemma length_filter_succ: forall A `{IA: Inhab A} (f: A -> bool) (l: list A) (iv: int),
    0 <= iv  ->
    iv < length l ->
    length (filter (fun x : A => f x) (take (iv + 1) l)) =
      length (filter (fun x : A => f x) (take iv l)) + (if f l[iv] then 1 else 0).
Proof.
  intros A IA f l iv H0iv Hiv.
  rewrite (@take_pos_last A IA l (iv + 1)); try (apply int_index_prove; try math).
  rewrite filter_last.
  math_rewrite (iv + 1 - 1 = iv).
  rewrite If_istrue.
  case_eq (f l[iv]); intros Hliv; try rewrite length_last; rew_list; try math.
Qed.

Lemma take_filter_succ: forall A `{IA: Inhab A} (f: A -> bool) (l: list A) iv jv,
    f l[iv] -> jv < iv -> iv < length l ->
    jv = length (filter (fun x : A => f x) (take iv l)) ->
    take (jv + 1) (filter (fun x : A => f x) l) =
      take jv (filter (fun x : A => f x) l) & l[iv].
Proof.
  intros A IA f l iv jv Hfliv Hjviv Hiv Hjv.
  rewrite (@take_pos_last A IA _ (jv + 1)).
  - {
      case (@take_is_prefix A (iv + 1) l); intros l_suf Hlsuf.
      math_rewrite (jv + 1 - 1 = jv).
      rewrite Hlsuf at 2.
      rewrite (@take_pos_last A IA l (iv + 1)); try (apply int_index_prove; try math).
      rewrite filter_app; rewrite filter_last.
      math_rewrite (iv + 1 - 1 = iv). rewrite If_l; auto.
      rewrite read_app.
      rewrite If_l; try (rewrite length_last; rewrite Hjv; math).
      rewrite read_last_case.
      rewrite If_l; try (rewrite Hjv; math).
      auto.
    }
  - {
      apply int_index_prove; try math.
      rewrite <- length_eq. math_rewrite (jv + 1 - 1 = jv).
      rewrite Hjv.
      assert (0 <= iv) as Hivgt by math.
      case (@take_is_prefix A (iv + 1) l); intros l_suf Hlsuf.
      rewrite Hlsuf at 2.
      rewrite filter_app; rewrite length_app.
      rewrite (@take_pos_last A IA l (iv + 1)); try (apply int_index_prove; try math).
      math_rewrite (iv + 1 - 1 = iv).
      rewrite filter_last; rewrite If_l; auto; rewrite length_last.
      math.
    }
Qed.

Lemma drop_write_zero: forall A `{IA: Inhab A} (xs: list A) v i,
    0 <= i < length xs ->
    (drop i xs)[0:=v] =
      v :: drop (i + 1) xs.
Proof.
  intros A IA xs v i Hi.
  rewrite (@drop_cons_unfold A IA); try math.
  rewrite update_zero; auto.
Qed.

Lemma filter_take_propagate: forall A `{IA: Inhab A} (l: list A) (f: A -> bool) iv jv,
    f l[iv] -> 0 <= iv < length l ->
    jv = length (filter (fun x : A => f x) (take iv l)) ->
    (filter (fun x : A => f x) l)[jv] = l[iv].
Proof.
  introv Hfliv [Hlen_gt Hlen] Hjv.
  pose proof (length_filter_take_leq_base f l Hlen_gt) as Hjvlen.
  rewrite <- Hjv in Hjvlen.
  rewrite <- (@list_eq_take_app_drop _ iv l) at 1; try math.
  rewrite filter_app.
  rewrite read_app.
  rewrite If_r; try math.
  rewrite <- Hjv.
  math_rewrite (jv - jv = 0).
  rewrite (@drop_cons_unfold A IA); try (split; math).
  rewrite filter_cons; rewrite If_l; auto; rewrite read_zero.
  auto.
Qed.  

Definition Vector A `{Enc A} (l: list A) (p: loc) : hprop :=
  \exists (data: loc) (D: list A) (G: list A),
     (* p points to the vector record w. size *)
      p ~> Record `{ vec' := data; size' := length l } \*
     (*  data points to an array modelled by D *)
      data ~> Array D \*
     (* D shares a prefix with l *)
      \[ D = l ++ G ].

Lemma array_fill_app: forall (A: Type) `{EA: Enc A} (i j: int) (x: A) (l m r : list A) data,
  i = length l -> j = length m ->
  SPEC (Array_ml.fill data i j x)
  PRE (data ~> Array (l ++ m ++ r))
  POSTUNIT (data ~> Array (l ++ make j x ++ r)).
Proof.
  intros A EA i j x l m r data Hi Hj; xcf.
  xseq.
  xassert. {
  xif; try (intros Hfalse; math); intros Higt0.
  xif; try (intros Hfalse; math); intros Hjgt0.
  xapp; xvals. xvals. rewrite !length_app; rewrite <- Hi; rewrite <- Hj; math.
  }
Admitted.
  

Lemma filter'_spec (A: Type) `{EA: Enc A} `{IA: Inhab A} : forall (l: list A) (p:loc) (f: val) (f_p: A -> bool),
    (forall (x: A),
        SPEC_PURE (f x)
         POST \[= f_p x]
    ) ->
    SPEC (filter'__ f p)
    PRE (p ~> Vector l)
    POSTUNIT (p ~> Vector (List.filter f_p l)).
Proof.
  xcf.
  xapp;=>i. xapp;=>j.
  xunfold Vector; xpull;=> data D G HD.
  xapp.
  xlet.
  xseq.
  asserts loop_spec:  (
          forall (iv jv: int),
          0 <= iv -> 0 <= jv ->
          jv = length (filter f_p (take iv l)) ->
          jv <= iv ->
          iv <= length l ->
          SPEC (loop tt)
          PRE ( i ~~> iv \* j ~~> jv \*
             data ~> Array ((take jv (filter f_p l)) ++
                            drop jv D))
          INV (p ~~~> `{ vec' := data; size' := length l})
          POST (fun (_:  unit) => 
             i ~~> (length l) \* j ~~> (length (filter f_p l)) \*
             data ~> Array ((filter f_p l) ++ drop (length (filter f_p l)) D))). {
    intros iv.
    induction_wf IH: (upto (length l)) iv.
    intros jv Hivgt Hjvgt Hjvsem Hivjv Hivlt; apply Spec_loop; clear Spec_loop.
    xapp.
    xif ;=> Hiv.
    - xapp.
      xapp.
      xapp. {
        apply int_index_prove; try math.
        rewrite <- length_eq.
        rewrite length_app.
        rewrite length_take_nonneg; try math.
        rewrite length_drop_nonneg; try (rewrite HD; rew_list; math).
        rewrite Hjvsem. split; try math; apply length_filter_take_leq.
      }
      rewrite read_app.
      rewrite length_take; try math.
      rewrite Z.max_r; try math.
      assert (Hivlt := Hivlt).
      rewrite If_r; try math.
      rewrite read_drop; try (rewrite HD; rew_list; math);
        try (apply int_index_prove; try math; try (rewrite HD; rew_list; math)).
      math_rewrite (jv + (iv - jv) = iv).
      assert (D[iv] = l[iv]) as Hliv by
          (rewrite HD; rewrite read_app; rewrite If_l; try math; auto).
      rewrite Hliv.
      xapp (H l[iv]).
      xif ;=> Hfp_iv.
      * xapp. xapp.
        xif.
        ** intro Higt.
           xapp.
           xapp.
           xapp. {
             apply int_index_prove; try math.
             rewrite <- length_eq.
             rewrite length_app.
             rewrite length_take_nonneg; try math.
             rewrite length_drop_nonneg; try (rewrite HD; rew_list; math).
             rewrite Hjvsem. split; try math; apply length_filter_take_leq.
           }
           xapp.
           xapp.
           xapp. {
             apply int_index_prove; try math.
             rewrite <- length_eq.
             rewrite length_app.
             rewrite length_take_nonneg; try math.
             rewrite length_drop_nonneg; try (rewrite HD; rew_list; math).
             rewrite Hjvsem. split; try math; apply length_filter_take_leq.
           }
           xapp.
           xapp.
           {
             assert (jv <= length (filter (fun x => f_p x) l)) as Hjlt 
                 by (rewrite Hjvsem; apply length_filter_take_leq).
             xapp; try math. { unfold upto; split; try math. }
             { rewrite (@length_filter_succ A IA);
                 try math; rewrite Hjvsem; rewrite Hfp_iv; auto. }
             { rewrite read_app; try math.
               rewrite length_take; try math.
               rewrite If_r; try math.
               math_rewrite (iv - Z.max 0 jv = iv - jv).
               rewrite HD.
               rewrite read_drop; try (rew_list; math);
               try (apply int_index_prove; try math; rew_list; math).
               math_rewrite (jv + (iv - jv) = iv).
               rewrite read_app.
               rewrite If_l; try math.
               erewrite (@update_app_r _ _ 0 _ jv); try math;
                 try (rewrite length_take; try math).
               rewrite (@take_filter_succ A IA _ l iv jv); auto.
               case_eq l;
                 try (intro Hnil; rewrite Hnil in Hiv; rewrite length_nil in Hiv; math).
               intros l_fst l_lst Hl_fst.
               rewrite drop_write_zero; try (rew_list; math);
                 try (rewrite <- Hl_fst; rewrite length_app; math).
               rewrite app_cons_r. auto.
               auto.
             }
             {
               xsimpl.
             }
           }
        ** intros Hcond.
           assert (iv = jv) as Heq by math.
           xvals.
           xseq.
           xapp.
           xapp.
           xapp; try math. { unfold upto; split; try math. }
           { rewrite (@length_filter_succ A IA);
               try math; rewrite Hjvsem; rewrite Hfp_iv; auto. }
           {
             rewrite Heq in *.
             rewrite (@drop_cons_unfold A IA);
               try (rewrite HD; rew_list; math).
             rewrite (@take_last_unfold A IA _ (jv + 1)); try split; try math.
             math_rewrite (jv + 1 - 1 = jv).
             rewrite (@filter_take_propagate A IA l f_p jv jv); try auto; try math.
             rewrite Hliv; rewrite app_cons_r; auto.
             rewrite <- (@list_eq_take_app_drop _ (jv + 1) l) at 1; try math.
             rewrite filter_app; rewrite length_app.
             rewrite (@length_filter_succ _ IA); try math.
             rewrite Hfp_iv; rewrite <- Hjvsem.
             math.
           }
           {
             xsimpl.
           }
      * xapp.
        xapp; try math. { unfold upto; split; try math. }
        {
          rewrite (@length_filter_succ A IA); try math.
          rewrite <- If_istrue; rewrite If_r; auto.
          math.
        }
        {
          xsimpl.
        }
      * rewrite Hjvsem.
        rewrite <- (@list_eq_take_app_drop _ iv l) at 2; try math.
        rewrite filter_app; rewrite length_app.
        math.
    - xvals; try math.
      {
        assert (iv = length l) as Hleniv by math.
        rewrite Hjvsem; rewrite Hleniv; rewrite take_full_length; auto.
      }
      {
        assert (iv = length l) as Hleniv by math.
        rewrite Hjvsem; rewrite Hleniv; rewrite !take_full_length; auto.
      }      
  }
  xapp loop_spec; try math;
    try (rewrite take_zero; rewrite filter_nil; rewrite length_nil; auto).
  xapp.
  xif ;=> Hlengt0;   try (xvals; xif ;=> Hf; try (xvals; xapp; try (xapp; xsimpl; try auto; try math; try (rewrite filter_eq; auto))); try ((contradiction Hf; try exact I))).
  xapp. xapp. xvals.
  xif ;=> Hlenltlen;
    try (xvals; xapp; try (xapp; xsimpl; try auto; try math; try (rewrite filter_eq; auto))).
  xapp. xapp.
  apply int_index_prove; try math;
    try (rewrite <- length_eq; rewrite length_app; math).
  xapp. xapp. xapp. xapp.
  rewrite HD at 1. rewrite drop_app_l; try math. 
  xapp array_fill_app; try auto; try (rewrite length_drop_nonneg; math).
  xapp.
  xapp; xsimpl; try auto; try math; try (rewrite filter_eq; auto).
Qed.
