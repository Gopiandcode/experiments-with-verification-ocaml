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


Fixpoint list_drop (A: Type) (n: nat) (ls: list A) :=
  match n, ls with
  | O, rest => rest
  | S n, h :: t => drop n t
  | S n, nil => nil
  end.


Fixpoint list_take_drop (A: Type) (n: nat) (ls: list A) :=
  match n, ls with
  | O, rest => (nil, rest)
  | S n, h :: t =>
      let (take, drop) := list_take_drop n t in
      (h :: take, drop)
  | S n, nil => (nil, nil)
  end.

Eval compute in (list_take_drop 3 (1 :: 2 :: 3 :: 4 :: 5 :: nil)).

Lemma list_take_drop_split (A: Type): forall (n: nat) (ls: list A),
    (n <= List.length ls)%nat ->
    let (take, drop) := list_take_drop n ls in
    ls = take ++ drop.
Proof.
  intros n ls; gen n; induction ls.
  - intros n. simpl. intros Hltn0. apply le_n_0_eq in Hltn0.
    rewrite <- Hltn0; simpl. rewrite app_nil_r.
    auto.
  - simpl. intros n; case n; simpl.
    * intros _. rewrite app_nil_l. auto.
    * clear n; intros n Hn. apply le_S_n in Hn.
      pose proof (IHls n Hn).
      case_eq (list_take_drop n ls); intros take' drop' Heq.
      rewrite Heq in H.
      rewrite H.
      rewrite app_cons_l.
      auto.
Qed.

Lemma filter'_spec (A: Type) `{EA: Enc A} : forall (l: list A) (p:loc) (f: val) (f_p: A -> bool)
                            (* (f_p: A -> bool) *),
    (forall (x: A),
        SPEC_PURE (f x)
         POST \[= f_p x]
    ) ->
    SPEC (filter'__ f p)
    PRE (Vector l p)
    POSTUNIT (Vector (List.filter f_p l) p).
Proof.
  intro l; induction_wf IH: list_sub l. intros.
  xcf.
  xapp;=>i.
  xapp;=>j.
  xunfold Vector; xpull;=> data D G HD.
  xapp.
  xlet.
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
