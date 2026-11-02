(** Public finite Cartesian products for Federer (1969), 2.6.5, p. 119 Every
    proof uses the sealed first-factor and successor laws. Stage n
    represents n+1 factors, with no empty-product convention silently
    imposed on arbitrary outer measures. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP ProductMeasureUP ProductMeasure ProductRectangleValue
  CountablyMeasurableUP CountablyMeasurableProduct FiniteCartesianMeasureUP FiniteCartesianMeasureSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_cartesian_measure]: finite-product
    family of Federer 2.6.5, p. 119, exposed through
    its proved abstract laws rather than recursive implementation. *)
Definition finite_cartesian_measure (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)) :=
  @FiniteCartesianMeasure.value R X alpha h_alpha.
Arguments finite_cartesian_measure {R X alpha} h_alpha n A.

(** Source for [finite_cartesian_measure_specification]: inductive laws of
    Federer 2.6.5, p. 119 *)
Lemma finite_cartesian_measure_specification (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)) :
  is_finite_cartesian_measure_family alpha (finite_cartesian_measure h_alpha).
Proof. exact: FiniteCartesianMeasure.laws. Qed.

(** Source for [finite_cartesian_measure_first]: the single
    factor base of Federer 2.6.5, p. 119. *)
Lemma finite_cartesian_measure_first (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)) :
  finite_cartesian_measure h_alpha 0%N = @alpha 0%N.
Proof. exact: finite_cartesian_first_law (finite_cartesian_measure_specification h_alpha). Qed.

(** Source for [finite_cartesian_measure_is_measure]: each
    finite product measures its Cartesian carrier, Federer
    2.6.5, p. 119, by 2.6.1, p. 115. *)
Lemma finite_cartesian_measure_is_measure (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)) n :
  is_measure (finite_cartesian_measure h_alpha n).
Proof.
case: n=> [|n].
- rewrite finite_cartesian_measure_first; exact: h_alpha.
- exact: product_measure_measure_law (finite_cartesian_successor_law
  (finite_cartesian_measure_specification h_alpha) n).
Qed.

(** Source for [finite_cartesian_measure_successor]: the
    inductive binary product in Federer 2.6.5, p. 119,
    derived from uniqueness of its abstract specification. *)
Lemma finite_cartesian_measure_successor (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)) n :
  finite_cartesian_measure h_alpha n.+1 =
    product_measure (finite_cartesian_measure_is_measure h_alpha n) (h_alpha n.+1).
Proof.
exact: product_measure_unique
  (finite_cartesian_successor_law (finite_cartesian_measure_specification h_alpha) n)
  (product_measure_specification (finite_cartesian_measure_is_measure h_alpha n) (h_alpha n.+1)).
Qed.

(** Source for [finite_cartesian_measure_countable]: Supporting Federer
    2.6.5, p. 119. *)
Theorem finite_cartesian_measure_countable (R : realType) (X : nat -> choiceType)
    (alpha : forall j, set (X j) -> \bar R) (h_alpha : forall j, is_measure (@alpha j)) :
  (forall j, measure_countably_measurable (@alpha j) setT) ->
  forall n, measure_countably_measurable (finite_cartesian_measure h_alpha n) setT.
Proof.
move=> hc; elim=> [|n ih].
- rewrite finite_cartesian_measure_first; exact: hc.
- rewrite finite_cartesian_measure_successor.
  exact: product_whole_countably_measurable ih (hc n.+1).
Qed.
