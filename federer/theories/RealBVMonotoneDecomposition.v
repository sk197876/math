(** Federer (1969), 2.9.19, p. 164: reduce a real function g of locally
    bounded variation to the nondecreasing functions s and s-g, with s the
    arc-length function of 2.5.16, p. 109. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CurveArcLength MeasureAlmostUP MeasureAlmostBasic
  LebesgueScalarMeasure RealCurveDerivativeUP RealCurveDerivativeLaws MonotoneStieltjesDifferentiation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_bv_arc_remainder_monotone]: direct monotonicity of s-g
    used in Federer 2.9.19, p. 164, from the distance/variation inequality
    of 2.5.16, p. 109. The scalar increment g(b)-g(a) is at most its
    absolute value, which is at most s(b)-s(a). *)
Lemma real_bv_arc_remainder_monotone (R : realType) (g : R -> real_line_metric R) :
  curve_locally_finite_variation g -> forall a b : R, a<=b ->
    arc_length g a-g a<=arc_length g b-g b.
Proof.
move=> hg a b hab.
have hbound := @arc_length_distance R [the metricType R of real_line_metric R] g hg a b hab.
rewrite real_line_metric_distanceE distrC in hbound.
have hinc := le_trans (ler_norm (g b-g a)) hbound.
lra.
Qed.

(** Source for [real_bv_joint_derivatives_ae]: direct existence of s' and
    g'=s'-(s-g)' in Federer 2.9.19, p. 164 Apply the proved monotone
    differentiability theorem twice and the proved finite subtraction law on
    the common conull set. The derivative of s is nonnegative. The equality
    with |g'| is the separate remaining variation argument. *)
Theorem real_bv_joint_derivatives_ae (R : realType) (g : R -> real_line_metric R) :
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v w : R,
    has_real_curve_derivative g x v /\ has_real_curve_derivative (arc_length g) x w /\ 0<=w].
Proof.
move=> hg.
have hsmono : forall a b : R, a<=b -> arc_length g a<=arc_length g b.
  move=> a b hab; exact (@arc_length_monotone R [the metricType R of real_line_metric R] g hg a b hab).
have hkmono := @real_bv_arc_remainder_monotone R g hg.
have hS := @monotone_real_derivative_exists_ae R (arc_length g) hsmono.
have hK := @monotone_real_derivative_exists_ae R (fun t => arc_length g t-g t) hkmono.
have hboth := measure_almost_everywhere_and (lebesgue_scalar_is_measure R) hS hK.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hboth).
move=> x [[w [hw hSw]] [z [hz hKz]]].
exists (w-z),w; split; last by split.
have heq : (fun t => arc_length g t-(arc_length g t-g t))=g.
  by apply: funext=> t; ring.
have hdiff := @has_real_curve_derivative_subtract R (arc_length g)
  (fun t => arc_length g t-g t) x w z hSw hKz.
by rewrite heq in hdiff.
Qed.
