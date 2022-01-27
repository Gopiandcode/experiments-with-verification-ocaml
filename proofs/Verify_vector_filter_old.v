Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A IA.

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import Vector_filter_old.

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
    0 < i < length l ->
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
    f l[iv] ->
    jv = length (filter (fun x : A => f x) (take iv l)) ->
    (filter (fun x : A => f x) l)[jv] = l[iv].
    

Definition Vector A `{Enc A} (l: list A) (p: loc) : hprop :=
  \exists (data: loc) (D: list A) (G: list A),
     (* p points to the vector record w. size *)
      p ~> Record `{ vec' := data; size' := length l } \*
     (*  data points to an array modelled by D *)
      data ~> Array D \*
     (* D shares a prefix with l *)
      \[ D = l ++ G ].

Lemma filter'_spec (A: Type) `{EA: Enc A} `{IA: Inhab A} : forall (l: list A) (p:loc) (f: val) (f_p: A -> bool)
                            (* (f_p: A -> bool) *),
    (forall (x: A),
        SPEC_PURE (f x)
         POST \[= f_p x]
    ) ->
    SPEC (filter'__ f p)
    PRE (Vector l p)
    POSTUNIT (Vector (List.filter f_p l) p).
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
             
           }
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
             }
             {
               xsimpl.
             }

           xapp; try math.

        contradiction Hcond.
        math.

  }
  xapp loop_spec.

  xapp.
  cuts HSpec:
    (forall (iv: int), iv <= length l ->
                         let (D_pre, D_post) := list_take_drop (Z.to_nat iv) D in
                         let (D_pre', D_post') := list_take_drop (Z.to_nat (min (iv + 1) (length l))) D in
                         SPEC (loop val_unit)
                              PRE (
                                i ~~> iv \*
                                  j ~~> (List.length (List.filter f_p D_pre)) \*
                                  data ~> Array ((List.filter f_p D_pre) ++ list_drop (List.length (List.filter f_p D_pre)) D)
                              )
                              POSTUNIT (
                                i ~~> (min (iv + 1) (length l)) \*
                                  j ~~> (List.length (List.filter f_p D_pre')) \*
                                  data ~> Array ((List.filter f_p D_pre') ++ list_drop (List.length (List.filter f_p D_pre')) D)
                              )
    ).
  

  (* xletrec *)
  (*   (fun (f: val) => *)
  (*      forall (iv: int), iv <= length l -> *)
  (*      let (D_pre, D_post) := list_take_drop (Z.to_nat iv) D in *)
  (*      let (D_pre', D_post') := list_take_drop (Z.to_nat (min (iv + 1) (length l))) D in *)
  (*      SPEC (f val_unit) *)
  (*      PRE ( *)
  (*          i ~~> iv \* *)
  (*          j ~~> (List.length (List.filter f_p D_pre)) \* *)
  (*          data ~> Array ((List.filter f_p D_pre) ++ list_drop (List.length (List.filter f_p D_pre)) D) *)
  (*      ) *)
  (*      POSTUNIT ( *)
  (*          i ~~> (min (iv + 1) (length l)) \* *)
  (*          j ~~> (List.length (List.filter f_p D_pre')) \* *)
  (*          data ~> Array ((List.filter f_p D_pre') ++ list_drop (List.length (List.filter f_p D_pre')) D) *)
  (*      ) *)
  (*   ). *)
  (* { *)
  (*   intros iv Hiv. *)
  (*   case_eq (list_take_drop (to_nat iv) D); intros D_pre D_post HDiv. *)
  (*   case_eq (list_take_drop (to_nat (min (iv + 1) (length l))) D); intros D_pre' D_post' HDiv'. *)
  (*   xapp. *)
  (*   apply Body_loop. *)
  (*   xsimpl. *)

  (* } *)

  (* xapp. *)
  (* xseq. *)
  (* xwhile_inv_basic_measure (fun (b: bool) (m: int) => \[True]). *)
  (* xwhile_inv_skip. *)
  (* xgo. *)
  (* xseq. *)
  (* xgo. *)

  
Admitted.
