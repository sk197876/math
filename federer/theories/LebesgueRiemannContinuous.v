(** Supporting continuous-integrand version of Federer (1969), 2.5.17, p.
    111, for the elementary evaluations in 2.6.3(2), pp. 117–118. A compact
    cutoff is proved to preserve the integrand on the interval, so global
    compact support is unnecessary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension SummableRealFunctionUP MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence StieltjesSums StieltjesIntegral StieltjesContinuityPoints
  LebesgueScalarMeasure LebesgueRiemannSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_riemann_continuous_segment]: supporting
    identification of a continuous Riemann integral with the
    actual L^1 integral on [a,b], Federer 2.5.17,
    p. 111, used in 2.6.3(2), pp. 117–118.
    The extension from K(R) is justified by a proved cutoff
    and exact agreement on the interval. *)
Theorem lebesgue_riemann_continuous_segment (R : realType) (F : R -> R) (a b : R) :
  continuous F -> a < b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (real_total_integrand F) (stieltjes_integral (fun x => x) F a b)%:E.
Proof.
move=> hF hab.
have [G [hG he]] := continuous_segment_compact_extension a b hF.
have hi := lebesgue_riemann_compact_segment hG hab.
have hv := @stieltjes_integral_eq_on_integrand R (fun x => x) G F a b (ltW hab) he.
rewrite hv in hi.
apply: (@measure_integral_graph_equivalent R R _ _ _ _ _ hi)=> x y.
case: (pselect (`[a,b] x))=> hx.
- rewrite !partial_function_zero_extension_on // !real_total_integrand_graph.
  have hx' : a <= x <= b by move: hx; rewrite /= in_itv.
  by rewrite (he x hx').
- by rewrite !partial_function_zero_extension_off.
Qed.
