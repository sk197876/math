(** Federer (1969), 2.9.25, p. 169: the absolute-continuity step uses
    2.4.4(7), p. 82, and the subset convention of 2.4.10, p. 85. These
    supporting graph laws commute absolute value with restriction without
    changing the partial domain. No relevant entry occurs in the local
    Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP
  PartialFunctionPostcomposition PartialAbsolutePartsGraph PartialZeroExtension
  PartialZeroExtensionLaws MeasureUP MeasureSubsetIntegral MeasureIntegralAbsolute
  MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_extension_absolute_graph]: supporting exact
    graph identity for the subset absolute-integral estimate in
    Federer 2.9.25, p. 169, by 2.4.10, p. 85.
    This holds for arbitrary partial extended-real integrands. *)
Lemma zero_extension_absolute_graph (R : realType) (X : Type)
    (A : set X) (f : partial_function X (extended_real_line R)) x y :
  partial_function_graph (partial_extended_function_absolute_value
    (partial_function_zero_extension (0 : extended_real_line R) A f)) x y <->
  partial_function_graph (partial_function_zero_extension (0 : extended_real_line R) A
    (partial_extended_function_absolute_value f)) x y.
Proof.
exact: (@partial_zero_extension_postcompose X (extended_real_line R) (extended_real_line R)
  0 0 A f (fun z => `|z|) x y abse0).
Qed.

(** Source for [subset_integral_absolute_bound]: supporting application of
    Federer 2.4.4(7), p. 82, in 2.9.25, p. 169 Retain the actual integral of
    the absolute value, including an infinite value if necessary. *)
Lemma subset_integral_absolute_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) (z : R) :
  is_measure_subset_integral mu A f z%:E -> exists J : \bar R,
    is_measure_subset_integral mu A (partial_extended_function_absolute_value f) J /\
    `|z|%:E<=J.
Proof.
move=> hI; have [J [hJ hb]] := measure_integral_absolute_bound hm hI.
exists J; split; last by move: hb; rewrite abse_EFin.
exact: measure_integral_graph_equivalent (zero_extension_absolute_graph A f) hJ.
Qed.
