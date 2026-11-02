(** Federer (1969), 2.4.11, proof p. 86: restriction of a nonnegative
    summable function to A has a nonnegative integral bounded by the
    original integral. Source context: PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP PartialExtendedOrderLoci
  MeasurableZeroExtension ZeroExtensionNonnegative MeasureIntegralUP MeasureIntegralBounds
  MeasureNonnegativeIntegral MeasureIntegralComparison MeasureSubsetIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_zero_extension_integral_bound]:
    supporting subset comparison in Federer 2.4.11,
    proof p. 86. The original integral may be infinite;
    a finite original bound gives finiteness of the restriction. *)
Lemma nonnegative_zero_extension_integral_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) b :
  measure_measurable mu A -> is_measure_integral mu f b ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  let g := partial_function_zero_extension (0 : extended_real_line R) A f in
  is_measure_subset_integral mu A f (measure_lower_integral mu g) /\
    0 <= measure_lower_integral mu g /\ measure_lower_integral mu g <= b.
Proof.
move=> hA hf hp g.
have hgm := @measurable_zero_extension R X (extended_real_line R) mu hm 0 A f hA hf.1.
have hgp := @zero_extension_nonnegative_almost R X mu hm A f hp.
have [hi hpos] := @nonnegative_measurable_function_integral R X mu hm g hgm hgp.
split=> //; split=> //; apply: (@measure_integral_monotone R X mu hm g f _ b hi hf).
have hsub : A `<=` setT by move=> x hx.
have hcomp := @nonnegative_zero_extension_subset_order R X mu hm A setT f hsub hp.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hcomp)=> x [a [c [ha [hc hac]]]].
exists a,c; split=> //; split=> //.
exact: (partial_zero_extension_whole_graph (0 : extended_real_line R) f x c).1 hc.
Qed.
