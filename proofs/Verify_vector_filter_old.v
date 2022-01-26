Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
  (* Generalizable Variables . *)

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import Vector_filter_old.

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
          jv <= length (filter f_p l) ->
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
      }
      rewrite read_app.
      assert (length (take jv (filter (fun x : A => f_p x) l)) <= iv).
      eapply lt_le_trans.

      xapp (H (take jv (filter (fun x : A => f_p x) l) ++ drop jv D)[iv]).
      xif.
      *

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
