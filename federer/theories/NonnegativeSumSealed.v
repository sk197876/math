(** Federer (1969), 2.1.1, pp. 52-53: numerical sums over arbitrary sets.
    Finite sets and extended-real scalar arithmetic are background; the
    arbitrary summation operator and its laws are developed here. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSumUP NonnegativeSumConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type NonnegativeSumSignature.
(** Source for [value]: Federer 2.1.1(3), p. 52;
    abstract numerical summation operator for nonnegative functions. *)
Parameter value : forall (R : realType) (I : choiceType),
  set I -> (I -> \bar R) -> \bar R.
(** Source for [laws]: Federer 2.1.1(3), p. 52;
    the operator is characterized by its finite-subsum bounds. *)
Parameter laws : forall (R : realType) (I : choiceType)
  (A : set I) (f : I -> \bar R), is_nonnegative_sum A f (@value R I A f).
End NonnegativeSumSignature.

Module NonnegativeSum : NonnegativeSumSignature.
(** Source for [value]: Federer 2.1.1(3), p. 52;
    private choice of the established summation witness. *)
Definition value (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :=
  projT1 (cid (@nonnegative_sum_exists R I A f)).
(** Source for [laws]: Federer 2.1.1(3), p. 52;
    the chosen witness obeys the abstract specification. *)
Lemma laws (R : realType) (I : choiceType) (A : set I) (f : I -> \bar R) :
  is_nonnegative_sum A f (value A f).
Proof. exact: projT2 (cid (@nonnegative_sum_exists R I A f)). Qed.
End NonnegativeSum.
