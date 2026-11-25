(** Supporting section measurability for Federer (1969), 2.6.3(2), pp.
    117–118 A positive-coordinate section agrees on the positive half-line
    with a globally continuous clipped rational expression, and vanishes
    elsewhere. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostBasic BorelRegularMeasureUP TopologicalBorel BorelFunctionBasic
  MeasurableFunctionUP MeasurableTotalBasic MeasurableTotalPiecewise MeasureStepIntegralIdentification
  SummableRealFunctionUP LebesgueScalarMeasure CountableOrderIntervals
  RationalFubiniKernel RationalPrimitiveExpressions RationalPrimitiveContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_continuous_total_measurable]: supporting
    continuous-function case of Federer 2.3.2, p. 73,
    for L^1 from 2.5.17, p. 111, used for
    the section estimates in 2.6.3(2), pp. 117–118.
    Open preimages are Borel and hence measurable. *)
Lemma lebesgue_continuous_total_measurable (R : realType) (f : R -> real_line_metric R) :
  continuous f -> is_measure_measurable_function (@lebesgue_scalar_measure R) (partial_function_total f).
Proof.
move=> hf; constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true (lebesgue_scalar_is_measure R).
- move=> U hU; rewrite partial_function_total_preimage.
  apply: (borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  exact (@continuous_borel_function (Topological.clone R _) (real_line_metric R) f hf U hU).
Qed.

(** Source for [rational_positive_section_measurable]: supporting
    measurability of the section with fixed y>0 in Federer 2.6.3(2), pp.
    117–118 The discontinuity at zero is treated by a measurable partition,
    not by claiming global continuity. *)
Lemma rational_positive_section_measurable (R : realType) (y : R) :
  0 < y -> is_measure_measurable_function (@lebesgue_scalar_measure R)
    (partial_function_total (fun x => (rational_fubini_kernel x y : real_line_metric R))).
Proof.
move=> hy.
have hc : continuous (rational_clipped_first_density y) := rational_first_density_continuous hy.
have hA : measure_measurable (@lebesgue_scalar_measure R) [set x : R | 0 < x].
  apply: (borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  apply: open_borel_set; exact: order_strict_upper_ray_open.
have he : (fun x => (rational_fubini_kernel x y : real_line_metric R)) =
    (fun x => if pselect (0 < x) then rational_clipped_first_density y x else 0).
  apply: funext=> x; case: (pselect (0 < x))=> hx.
  - rewrite rational_fubini_kernel_positive //; symmetry.
    exact: rational_clipped_first_density_on hy (ltW hx).
  - have hx0 : x <= 0 by rewrite leNgt; exact/negP.
    exact: rational_fubini_kernel_nonpositive_left hx0.
rewrite he; apply: (@measurable_total_piecewise R R (real_line_metric R)
  _ (lebesgue_scalar_is_measure R) [set x : R | 0 < x] _ _ hA).
- exact: lebesgue_continuous_total_measurable hc.
- exact (@measurable_total_constant R R (real_line_metric R) _ (lebesgue_scalar_is_measure R) 0).
Qed.
