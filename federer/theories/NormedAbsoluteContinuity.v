(** Federer (1969), 2.9.22, pp. 167–168: all four equivalent
    absolute-continuity conditions extending 2.9.20, pp. 165–166, to normed
    curves. The proof follows the printed cycle (1)=>(2)=>(3)=>(4)=>(1).
    Actual norm derivative existence almost everywhere is an explicit
    intermediate premise, supplied by the already proved reflexive Banach
    theorem. No relevant Federer erratum entry applies. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP ContinuousDualUP CurveArcLength
  NormedCurveDerivativeUP NormedCurveAbsoluteContinuityUP MetricCurveAbsoluteContinuityUP
  NormedIndefiniteDerivativeVariationEquality NormedVariationIntegralAbsoluteContinuity
  NormedAbsoluteContinuityInducedMeasures NormedContinuousInducedIntegral
  MeasureAlmostUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_absolute_continuity_equivalences]: complete
    four-condition extension asserted by Federer 2.9.22,
    pp. 167–168, of 2.9.20, pp. 165–166. The primitive uses
    the actual vector integral of the exact partial derivative;
    the variation equality uses its actual norm subset integral;
    the finite-family law retains the printed strict cells and
    non-strict sums; condition (4) has relative closed-segment norm
    continuity and each actual scalar induced pair restricted to the
    open interval. The scalar pair is fixed before its measure claims. *)
Theorem normed_absolute_continuity_equivalences (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> real_norm_metric_space hN) (a b : R) :
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] -> a<b ->
  (normed_curve_indefinite_derivative_integral hN g a b <->
    normed_curve_variation_integral_equality hN g a b) /\
  (normed_curve_variation_integral_equality hN g a b <->
    is_absolutely_continuous_metric_curve g a b) /\
  (is_absolutely_continuous_metric_curve g a b <->
    normed_curve_continuous_induced_measures hN ed g a b).
Proof.
move=> hY hg he hab.
have h12 := @normed_indefinite_derivative_integral_variation_equality R E N hN g a b hY hg he (ltW hab).
have h23 := @normed_variation_integral_equality_absolute_continuity R E N hN g a b hg he hab.
have h34 := @normed_absolute_continuity_induced_measures R E D N hN ed DN hD g a b hg.
have h41 := @normed_continuous_induced_integral_representation R E D N hN ed DN hD g a b hY hg he hab.
split.
- split; [exact h12|move=> h2; exact: h41 (h34 (h23.1 h2))].
- split; first exact h23.
  split; [exact h34|move=> h4; exact: h23.1 (h12 (h41 h4))].
Qed.
