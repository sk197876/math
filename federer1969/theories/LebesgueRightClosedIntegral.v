(** Federer (1969), 2.9.24, p. 169: the step cells are (u,v], while
    primitive integrals are stated on [u,v]. The left endpoint has zero
    Lebesgue measure, so the actual integral is unchanged. This is 2.4.3(2),
    p. 81, with the subset convention of 2.4.10, p. 85. The local Federer
    erratum has no entry here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP
  MeasureIntegralUP MeasureSubsetIntegral SubsetIntegralNullReplacement LebesgueScalarMeasure
  TotalScalarCutoff SummableRealFunctionUP MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_right_closed_segment_integral]: supporting
    omission of the left endpoint in the cell integral of
    Federer 2.9.24, p. 169. Actual partial integrands and
    signed infinite integral values are allowed. *)
Lemma lebesgue_right_closed_segment_integral (R : realType)
    (f : partial_function (real_line_metric R) (extended_real_line R)) (u v : R) z :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v] f z ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `]u,v] f z.
Proof.
move=> hi; apply: (@subset_integral_null_replacement R (real_line_metric R)
  (@lebesgue_scalar_measure R) f `[u,v] `]u,v] [set u] z
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_singleton u) _ hi)=> x hx.
have hxu : x!=u by apply/eqP=> he; exact: hx he.
rewrite /= !in_itv /= lt_neqAle eq_sym hxu /=.
by split.
Qed.

(** Source for [lebesgue_right_closed_cutoff_integral]: supporting
    total real cutoff version of the cell integral in Federer
    2.9.24, p. 169. A finite cell value remains exactly
    the integral of the zero-extended total real function. *)
Lemma lebesgue_right_closed_cutoff_integral (R : realType) (f : R -> R) (u v : R) z :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[u,v] (real_total_integrand f) z ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (total_scalar_cutoff (`]u,v] : set R) f)) z.
Proof.
move=> hi.
have hJ := lebesgue_right_closed_segment_integral hi.
exact: measure_integral_graph_equivalent (total_scalar_cutoff_integrand_graph _ _) hJ.
Qed.
