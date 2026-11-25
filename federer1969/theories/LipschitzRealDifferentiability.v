(** Federer (1969), 3.1.6, p. 216: the one-dimensional
    input to Rademacher's theorem is the bounded-variation theorem
    2.9.19, pp. 163–165. No external differentiability result is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP
  CurveVariationUP CurveArcLength LipschitzCurveVariation StieltjesImageMeasures
  RealBVDifferentiation LebesgueScalarMeasure MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [lipschitz_real_curve_differentiable_almost_everywhere]:
    the application of 2.9.19 in the proof of Federer 3.1.6,
    p. 216. Lipschitz control supplies locally finite variation;
    the induced measure pair exists by the proved laws of 2.5.17. *)
Theorem lipschitz_real_curve_differentiable_almost_everywhere (R : realType)
    (f : R->R) (M : R) :
  (forall s t, `|f s-f t|<=M*`|s-t|) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set s | exists v, has_real_curve_derivative f s v].
Proof.
move=> hM.
have hBV : curve_locally_finite_variation (f : R->real_line_metric R).
  apply: (lipschitz_curve_locally_finite_variation (L:=M)).
  move=> s t; rewrite real_line_metric_distanceE; exact: hM.
have [psip [psim hpair]] := induced_measure_pair_exists hBV.
have hdiff := (@federer_2_9_19 R f psip psim hBV hpair).1.
apply: (measure_almost_everywhere_mono (lebesgue_scalar_is_measure R) _ hdiff).
by move=> s [v [hv _]]; exists v.
Qed.
