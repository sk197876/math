(** Federer (1969), 2.4.10, p. 85: supporting reduction to a total
    nonnegative representative before the characteristic expansion. The
    existing total-extension theorem of 2.3.2 is followed by taking the
    positive part, which changes nothing almost everywhere for a nonnegative
    input. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableTotalExtension MeasurableExtendedParts MeasurableGraphEquivalence PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_nonnegative_total_representative]:
    supporting conull replacement for the characteristic-series
    proof of Federer 2.4.10, p. 85. Negative
    exceptional values, as well as undefined points, are removed. *)
Lemma measurable_nonnegative_total_representative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  exists F : X -> extended_real_line R,
    (forall x, 0 <= F x) /\ is_measure_measurable_function mu (partial_function_total F) /\
    measure_almost_equal mu f (partial_function_total F).
Proof.
move=> hf hp; have [g [he [ha hg]]] := @measurable_function_total_extension R X (extended_real_line R) mu hm f 0 hf.
pose F x := (extended_positive_part (g x) : extended_real_line R).
exists F; split; first by move=> x; exact: extended_positive_part_nonnegative.
split.
- have hpos := @measurable_extended_positive_part R X mu hm (partial_function_total g) hg.
  apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hpos)=> x y; split.
  + by move=> [z [hz ezy]]; rewrite -(hz : g x=z) in ezy.
  + move=> hy; exists (g x); by split.
- apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp)=> x [z [hz hz0]].
  exists z; split=> //; change (F x=z).
  by rewrite /F (he x z hz) /extended_positive_part max_l.
Qed.
