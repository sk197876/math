(** Federer (1969), 3.1.3(4), p. 213: measurability of equality
    with the approximate upper and lower limits. The equality locus
    requires actual values of both partial functions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureUP MeasureFiniteClosure
  MeasurableFunctionUP ExtendedRealOrderTopology PartialExtendedOrderLoci
  MeasurableExtendedComparisons.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_extended_agreement]: supporting measurable
    equality test in Federer 3.1.3(4), p. 213. Intersect the two weak
    comparisons from 2.3.2(2), p. 73; undefined values do not agree. *)
Lemma measurable_extended_agreement (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f g : partial_function X (extended_real_line R)) :
  is_measure phi -> is_measure_measurable_function phi f -> is_measure_measurable_function phi g ->
  measure_measurable phi (partial_function_agreement f g).
Proof.
move=> hm hf hg.
have he : partial_function_agreement f g=
    partial_extended_le_locus f g `&` partial_extended_le_locus g f.
  apply/seteqP; split.
  - move=> x [y [hyf hyg]]; split; exists y,y; by split=> //; split=> //; exact: lexx.
  - move=> x [[a [b [ha [hb hab]]]] [c [d [hc [hd hcd]]]]].
    have had := partial_function_single_valued ha hd.
    have hbc := partial_function_single_valued hb hc.
    rewrite -had -hbc in hcd.
    have habE : a=b by apply/eqP; rewrite eq_le hab hcd.
    exists a; split=> //; by rewrite habE.
rewrite he; apply: (@measure_measurable_intersection R X phi hm).
- exact: measurable_extended_weak_comparison hm hf hg.
- exact: measurable_extended_weak_comparison hm hg hf.
Qed.
