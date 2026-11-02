(** Federer (1969), 2.6.3(2), p. 118: under hypothetical product
    integrability, Fubini computes the integral over {0<x<a,0<y<m*a} as
    m/(1+m)^2. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground MeasureUP BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions RealOpenIntervals
  MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral MeasureIntegralSplitting
  ProductMeasure ProductRectangleMeasurability ProductFunctionFubini
  LebesgueScalarMeasure LebesgueProductIntegrands RationalFubiniKernel RationalIteratedIntegrals RationalRectangleIterate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_open_rectangle_measurable]: supporting
    measurability of the open rectangles in Federer
    2.6.3(2), p. 118, by 2.6.2(2),
    p. 115. Empty and degenerate intervals are allowed. *)
Lemma lebesgue_open_rectangle_measurable (R : realType) (a b : R) :
  measure_measurable
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (`]0,a[ `*` `]0,b[).
Proof.
have hI t : measure_measurable (@lebesgue_scalar_measure R) `]0,t[.
  apply: (borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
  apply: open_borel_set; apply: interval_open; by [].
exact: product_measure_rectangle_measurable (hI a) (hI b).
Qed.

(** Source for [rational_rectangle_integral_if_integrable]: the two
    successive Fubini evaluations in Federer 2.6.3(2), p. 118, retaining the
    hypothetical integrability premise used in the contradiction The upper
    y-endpoint b is arbitrary and positive. *)
Theorem rational_rectangle_integral_if_integrable (R : realType) (a b : R) :
  0 < a -> 0 < b ->
  is_measure_integrable
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (@rational_fubini_integrand R) ->
  is_measure_subset_integral
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (`]0,a[ `*` `]0,b[) (@rational_fubini_integrand R) (rational_second_primitive a b)%:E.
Proof.
move=> ha hb [z hi].
pose hm := lebesgue_scalar_is_measure R.
have hnu := product_measure_is_measure hm hm.
have [u [v [hui _]]] := (@measure_integral_measurable_split R (Choice.clone (R*R)%type _)
  _ hnu (`]0,a[ `*` `]0,b[) _ z (@lebesgue_open_rectangle_measurable R a b)).1 hi.
have hc := lebesgue_product_function_countably_measurable hui.1.
have hf := (@product_function_fubini R R R _ _ hm hm _ u hui hc).2.
have hh := @rational_rectangle_repeated_integral R a b ha hb.
have he := measure_integral_unique hf hh.
by rewrite -he.
Qed.

(** Source for [rational_scaled_rectangle_integral_if_integrable]: the
    scale-independent value m/(1+m)^2 printed in Federer 2.6.3(2), p. 118 No
    product integrability is asserted: it remains the explicit contradiction
    premise. *)
Corollary rational_scaled_rectangle_integral_if_integrable (R : realType) (a m : R) :
  0 < a -> 0 < m ->
  is_measure_integrable
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (@rational_fubini_integrand R) ->
  is_measure_subset_integral
    (product_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (`]0,a[ `*` `]0,m*a[) (@rational_fubini_integrand R) (m/(1+m)^+2)%:E.
Proof.
move=> ha hm hi; have hma : 0 < m*a by rewrite mulr_gt0.
have hh := @rational_rectangle_integral_if_integrable R a (m*a) ha hma hi.
by rewrite (rational_second_primitive_scaled_endpoint ha hm) in hh.
Qed.
