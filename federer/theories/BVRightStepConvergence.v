(** Federer (1969), 2.9.24, p. 169: the uniform right- endpoint step
    functions converge boundedly and Lebesgue almost everywhere on the
    interval to the BV function f. The exceptional continuity set comes from
    2.5.16, p. 109. The local Federer erratum has no entry for this step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground RealMetricCompleteness CurveVariationUP CurveArcLength
  CurveDiscontinuities MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureRestriction
  RestrictedAlmostEverywhere LebesgueScalarMeasure ScalarLebesgueBallContext
  ExtendedRealOrderLimit RealErrorOrderLimit RightStepApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bv_right_step_almost_limit]: supporting actual
    almost-everywhere convergence of f_n to f in Federer 2.9.24, p. 169 The
    restricting measure is Lebesgue measure on [a,b], and the left endpoint
    is explicitly removed as a null exception. The local BV case follows by
    segment retraction. *)
Theorem bv_right_step_almost_limit (R : realType) (f : R -> R) (a b : R) :
  curve_locally_finite_variation (f : R -> real_line_metric R) -> a<=b ->
  measure_almost_everywhere
    (measure_restrict (@lebesgue_scalar_measure R) (`[a,b] : set (real_line_metric R)))
    [set x | extended_order_limit
      (fun n => (uniform_right_step_approximation f a b n x)%:E) (f x)%:E].
Proof.
move=> hf hab.
have hm := lebesgue_scalar_is_measure R.
pose D := curve_jump_points (f : R -> real_line_metric R).
have hD : lebesgue_scalar_measure D=0%E.
  exact: scalar_lebesgue_countable_null (@curve_jump_points_countable R
    [the metricType R of real_line_metric R] f hf).
have hN : lebesgue_scalar_measure (D `|` [set a])=0%E.
  exact (@measure_null_union R (real_line_metric R) (@lebesgue_scalar_measure R)
    hm D [set a] hD (lebesgue_scalar_singleton a)).
have hgood : measure_almost_everywhere (@lebesgue_scalar_measure R) (~` (D `|` [set a])).
  by rewrite /measure_almost_everywhere setCK.
apply: (restricted_almost_everywhere_iff _ _ _).2.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) _ hm _ _ _ hgood)=> x hx hxI.
have /andP[hax hxb] : a<=x<=b by move: hxI; rewrite /= in_itv /=.
have hxa : x!=a by apply/eqP=> he; apply: hx; right; exact: he.
have hax' : a<x by rewrite lt_neqAle eq_sym hxa hax.
have hc : (f : real_line_metric R -> real_line_metric R) @
    (x : real_line_metric R) --> (f x : real_line_metric R).
  apply: contrapT=> hn; apply: hx; left.
  exact ((@curve_jump_points_iff R [the metricType R of real_line_metric R]
    f hf (@real_line_metric_complete R) x).2 hn).
apply: real_error_extended_order_limit=> e he.
exact (@uniform_right_step_pointwise_limit R f a b x hab hax' hxb hc e he).
Qed.
