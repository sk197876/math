(** Federer (1969), 2.6.3(1), p. 117: counting measure and its product with
    Lebesgue measure are Borel regular. This supporting factor lemma applies
    to any metric space. Counting measure is defined in Federer 2.1.2, p. 54 *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic CountingMeasure BorelRegularMeasureUP
  TopologicalBorel FiniteExceptionalBorel NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_singleton]: supporting singleton
    value of the counting factor in Federer 2.6.3(1),
    p. 117, from 2.1.2, p. 54. *)
Lemma counting_singleton (R : realType) (X : choiceType) (x : X) :
  @counting_measure R X [set x] = 1.
Proof. by rewrite counting_measure_sum nonnegative_sum_singleton // lee01. Qed.

(** Source for [counting_metric_borel_regular]: supporting Borel regularity
    of the counting factor in Federer 2.6.3(1), p. 117 A finite set is
    Borel, while the whole space is an equal-measure Borel hull of any
    infinite set. *)
Theorem counting_metric_borel_regular (R : realType) (X : metricType R) :
  is_borel_regular_measure (@counting_measure R X).
Proof.
constructor; first by move=> U _; exact: counting_measure_measurable.
move=> A; case: (pselect (finite_set A))=> hA.
- exists A; split=> //; split=> //; exact: finite_metric_set_borel.
- exists setT; split; first by move=> x _.
  split; first exact: open_borel_set openT.
  rewrite (@counting_measure_infinite R X A hA).
  apply/eqP; rewrite eq_le leey andbT.
  rewrite -(@counting_measure_infinite R X A hA).
  apply: (measure_mono (counting_measure_is_measure R X))=> x _; exact Logic.I.
Qed.
