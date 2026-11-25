(** Federer (1969), 4.1.5, p. 350:
    finite localized Euclidean Borel regular
    measures satisfy the standing context of
    2.9.8. The centered-ball Vitali law
    is the already proved application of
    2.8.18, p. 152. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP MeasureBasic BorelRegularMeasureUP MeasureDerivationContext
  CenteredBallRelations EuclideanFiniteMeasureVitali.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ereal_scope.

(** Source for [finite_euclidean_centered_derivation_context]:
    the original 2.8.18 and 2.9.8
    Euclidean context in Federer 4.1.5,
    p. 350, with finite localized mass. *)
Lemma finite_euclidean_centered_derivation_context (R:realType) n
    (mu:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R):
  is_measure mu ->is_borel_regular_measure mu ->mu setT< +oo ->
  is_measure_derivation_context mu (@centered_closed_ball_relation R
    (inner_metric_space (@euclidean_inner_productP R n))).
Proof.
move=>hm hr hFinite; constructor.
- constructor=>// A _.
  exact:le_lt_trans (measure_mono hm (subsetT A)) hFinite.
- exact:(euclidean_finite_measure_centered_vitali hm hr hFinite).
Qed.
