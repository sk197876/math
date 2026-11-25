(** Federer (1969), 2.6.3(2), p. 118: the repeated integral over an open
    positive rectangle. This module proves the actual repeated integral
    independently of any claim that the product integral exists. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialProductSections PartialZeroExtension SummableRealFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureConullZeroIntegral MeasureSubsetIntegral
  ParameterizedIntegral ParameterizedIntegralLaws RealSubsetIntegralGraph ProductRectangleRestriction
  LebesgueScalarMeasure LebesgueOpenSegmentIntegral RationalFubiniKernel RationalIteratedIntegrals RationalLebesgueIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rational_rectangle_repeated_integral]: the actual iterated
    integral over {0<x<a,0<y<b} equals a*b/(a+b)^2, supporting the displayed
    b=m*a calculation in Federer 2.6.3(2), p. 118 The set is exactly open,
    as printed. *)
Theorem rational_rectangle_repeated_integral (R : realType) (a b : R) :
  0 < a -> 0 < b ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (parameterized_integral (@lebesgue_scalar_measure R)
      (partial_product_horizontal_section
        (partial_function_zero_extension (0%E : extended_real_line R)
          (`]0,a[ `*` `]0,b[) (@rational_fubini_integrand R))))
    (rational_second_primitive a b)%:E.
Proof.
move=> ha hb; have hm := lebesgue_scalar_is_measure R.
pose v (y : R) := if pselect (`]0,b[ y) then rational_first_primitive y a else 0.
have houter : is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand v)
    (rational_second_primitive a b)%:E.
  have hi := lebesgue_closed_open_segment_integral (@rational_second_lebesgue_integral R a b ha hb).
  apply: ((@real_subset_integral_total R R _ `]0,b[ (fun y => rational_first_primitive y a)
    v _ _ _).1 hi).
  - move=> y hy; rewrite /v; by case: (pselect (`]0,b[ y)).
  - move=> y hy; rewrite /v; by case: (pselect (`]0,b[ y)).
apply: (@parameterized_integral_total_outer_transfer R R R _ _ hm _ (fun y => (v y)%:E)).
- apply: (@measure_almost_everywhere_mono R R _ hm setT _ _ (measure_almost_everywhere_true hm))=> y _.
  rewrite /= /v; case: (pselect (`]0,b[ y))=> hy /=.
  + have hyp : 0 < y by move: hy; rewrite /= in_itv /= => /andP[].
    have hi := lebesgue_closed_open_segment_integral (@rational_first_lebesgue_integral R y a hyp ha).
    refine (@measure_integral_graph_equivalent R R _ _ _ (rational_first_primitive y a)%:E _ hi).
    move=> x z.
    rewrite rectangle_restriction_horizontal_on //.

  + apply: (measure_almost_zero_integral hm).
    apply: (@measure_almost_everywhere_mono R R _ hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
    by apply/(rectangle_restriction_horizontal_off _ _ _ hy).
- apply: (@measure_integral_graph_equivalent R R _ _ _ _ _ houter)=> y z.
  by rewrite real_total_integrand_graph.
Qed.
