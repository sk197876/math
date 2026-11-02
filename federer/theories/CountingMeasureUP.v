(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSumUP NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_counting_measure]: Federer 2.1.2,
    p. 54, counting measure assigns the number of elements, or infinity.
    Abstract specification by cardinalities of finite subsets, using
    the finite-subsum law from 2.1.1(3), p. 52. The finite/infinite
    descriptions are proved from this specification in CountingMeasure.v. *)
Definition is_counting_measure (R : realType) (I : choiceType)
    (mu : set I -> \bar R) :=
  forall A, is_nonnegative_sum A (fun _ => (1 : R)%:E) (mu A).

(** Source for [counting_measure_unique]: Federer 2.1.2,
    p. 54, supporting uniqueness of the counting specification. *)
Lemma counting_measure_unique (R : realType) (I : choiceType)
    (mu nu : set I -> \bar R) :
  is_counting_measure mu -> is_counting_measure nu -> mu = nu.
Proof.
move=> hm hn; apply: funext=> A.
exact: nonnegative_sum_unique (hm A) (hn A).
Qed.
