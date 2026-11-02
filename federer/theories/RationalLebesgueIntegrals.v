(** Federer (1969), 2.6.3(2), pp. 117–118: the two finite rational integral
    evaluations, now for the actual sealed Lebesgue measure rather than only
    Riemann sums. Endpoints are retained as closed intervals; their
    singleton measures vanish by 2.5.17. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP
  LebesgueScalarMeasure LebesgueRiemannContinuous MeasureSubsetRealTransfer
  RationalFubiniKernel RationalPrimitiveExpressions RationalPrimitiveContinuity RationalRiemannIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rational_first_lebesgue_integral]: the first displayed
    integral in Federer 2.6.3(2), p. 117 The actual piecewise kernel differs
    from its continuous extension at zero only, a proved Lebesgue-null
    singleton. *)
Theorem rational_first_lebesgue_integral (R : realType) (y a : R) :
  0 < y -> 0 < a ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,a]
    (real_total_integrand (fun x => rational_fubini_kernel x y))
    (rational_first_primitive y a)%:E.
Proof.
move=> hy ha.
have hc : continuous (rational_clipped_first_density y) := rational_first_density_continuous hy.
have hi := @lebesgue_riemann_continuous_segment R (rational_clipped_first_density y) 0 a hc ha.
rewrite (rational_first_riemann_integral hy (ltW ha)) in hi.
apply: (@measure_subset_real_transfer_null R R _ (lebesgue_scalar_is_measure R)
  `[0,a] [set 0] (rational_clipped_first_density y) _ _ (lebesgue_scalar_singleton 0) _ hi).
move=> x hx hnx; move: hx; rewrite /= in_itv /= => /andP[hx _].
have hx0 : x != 0 by apply/eqP=> he; apply: hnx; exact: he.
have hxp : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
rewrite rational_fubini_kernel_positive //; exact: rational_clipped_first_density_on.
Qed.

(** Source for [rational_second_lebesgue_integral]: supporting second
    primitive evaluation in Federer 2.6.3(2), p. 118 Taking b=m*a gives the
    displayed expression in the book. *)
Theorem rational_second_lebesgue_integral (R : realType) (a b : R) :
  0 < a -> 0 < b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,b]
    (real_total_integrand (fun y => rational_first_primitive y a))
    (rational_second_primitive a b)%:E.
Proof.
move=> ha hb.
have hc : continuous (rational_clipped_second_density a) := rational_second_density_continuous ha.
have hi := @lebesgue_riemann_continuous_segment R (rational_clipped_second_density a) 0 b hc hb.
rewrite (rational_second_riemann_integral ha (ltW hb)) in hi.
apply: (@measure_subset_real_transfer_null R R _ (lebesgue_scalar_is_measure R)
  `[0,b] [set 0] (rational_clipped_second_density a) _ _ (lebesgue_scalar_singleton 0) _ hi).
move=> y hy _; move: hy; rewrite /= in_itv /= => /andP[hy _].
exact: rational_clipped_second_density_on.
Qed.

(** Source for [rational_second_scaled_lebesgue_integral]: the
    scale-independent m/(1+m)^2 value in Federer 2.6.3(2), p. 118 This is an
    actual Lebesgue subset integral, with both positive parameters retained. *)
Theorem rational_second_scaled_lebesgue_integral (R : realType) (a m : R) :
  0 < a -> 0 < m ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,m*a]
    (real_total_integrand (fun y => rational_first_primitive y a))
    (m/(1+m)^+2)%:E.
Proof.
move=> ha hm; have hma : 0 < m*a by rewrite mulr_gt0.
have hi := rational_second_lebesgue_integral ha hma.
by rewrite (rational_second_primitive_scaled_endpoint ha hm) in hi.
Qed.
