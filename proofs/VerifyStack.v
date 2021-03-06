
Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.

Implicit Types n m: int.
Implicit Types p q : loc.

From Proofs Require Import Stack.

Definition Stack A `{EA:Enc A} (L:list A) (r:loc) : hprop :=
      r ~~~> `{ Stack.contents' := L }.

Lemma Stack_eq : forall r A `{EA:Enc A} (L:list A),
  (r ~> Stack L) =
  (r ~~~> `{ Stack.contents' := L }).
Proof using. auto. Qed.

Arguments Stack_eq : clear implicits.

Lemma Stack_open : forall r A (L:list A),
    r ~> Stack L ==>
        r ~~~> `{ contents' := L }.
Proof using.
  dup 2.
  { intros. xunfold Stack. auto. 
  (* Try [hcancel 3] to see how it works *) }
  { intros. xunfolds~ Stack. }
Qed.

Lemma Stack_close : forall r A (L:list A) (n:int),
    r ~~~> `{ contents' := L } ==>
      r ~> Stack L.
Proof using. intros. xunfolds~ Stack. Qed.

Arguments Stack_close : clear implicits.

Hint Extern 1 (RegisterOpen (Stack _)) =>
       Provide Stack_open.
Hint Extern 1 (Xclose_Hint (Stack _)) =>
       Provide Stack_close.

Lemma create_spec : forall A `{EA:Enc A},
  SPEC (create tt)
    PRE \[]
    POST (fun s => s ~> Stack (@nil A)).
Proof using.
  xcf. xapp ;=> s. xunfolds~ Stack.
Qed.

Lemma push_spec : forall A `{EA:Enc A} (L:list A) (s:loc) (x:A),
  SPEC (push s x)
    PRE (s ~> Stack L)
    POSTUNIT (s ~> Stack (x::L)).
Proof using.
  (* Hint: use [xcf], [xapp], [xapps], [xpull], [xsimpl],
     [xopen], [xclose] and [rew_list] *)
  (* <EXO> *)
  xcf.
  xunfolds~ Stack.
  xapp. xapp. 
  xunfolds~ Stack. 
Qed.

Lemma pop_spec : forall A `{EA:Enc A} (L:list A) (s:loc),
  L <> nil ->
  SPEC (pop s)
    PRE (s ~> Stack L)
    POST (fun x =>
            match x with
            | None => \[False]
            | Some x => \exists L', \[L = x::L'] \* s ~> Stack L'
         end).
Proof using.
  introv HL. xcf.
  xunfolds~ Stack.
  xapp.
  xmatch.
  xapp.  xval.
  xunfolds~ Stack.
Qed.
