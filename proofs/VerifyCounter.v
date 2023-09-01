Set Implicit Arguments.

From CFML Require Import WPLib Stdlib.
From TLC Require Import LibListZ.
Generalizable Variables A.


From Proofs Require Import Counter.

(** Lazy values: a lazy value of type [a] is represented at type [unit->'a].
    [Lazyval P f] asserts that [f] is a lazy value whose evaluation produces
    a value satisfying the (pure) predicate [P]. *)
