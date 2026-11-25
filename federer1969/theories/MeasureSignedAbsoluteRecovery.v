(** Federer (1969), 2.4.14, p. 88: sufficiency of a fixed sign for equality
    between the absolute integral and the integral of the absolute value.
    These supporting null-modification arguments retain partial domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  PartialExtendedOrderLoci PartialAbsolutePartsGraph MeasureIntegralNegation
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureAbsoluteEquality
  MeasureIntegralAlmostEquality MeasureIntegralGraphEquivalence MeasureIntegralNegationLaw.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_absolute_integral_recovers]: the positive-sign
    sufficiency step in Federer 2.4.14, p. 88 The signed integrand agrees
    with its absolute value on a conull set, so its integral is recovered
    from that value. *)
Lemma nonnegative_absolute_integral_recovers (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) c :
  is_measure_integral mu (partial_extended_function_absolute_value f) c ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  is_measure_integral mu f c.
Proof.
move=> hi hp; apply: (@measure_integral_almost_equal R X mu hm _ _ c hi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp).
move=> x [z [hz hz0]]; exists z; split=> //; exists z; split=> //.
exact: gee0_abs hz0.
Qed.

(** Source for [nonpositive_absolute_integral_recovers]: the negative-sign
    sufficiency step in Federer 2.4.14, p. 88 Nonnegativity of -f recovers
    the negative integral value. *)
Lemma nonpositive_absolute_integral_recovers (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) c :
  is_measure_integral mu (partial_extended_function_absolute_value f) c ->
  measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_extended_function_negate f)) ->
  is_measure_integral mu f (-c).
Proof.
move=> hi hp.
have hnabs : is_measure_integral mu (partial_extended_function_absolute_value (partial_extended_function_negate f)) c.
  apply: (@measure_integral_graph_equivalent R X mu _ _ c _ hi)=> x z.
  exact (iff_sym (absolute_negation_graph f x z)).
have hn := @nonnegative_absolute_integral_recovers R X mu hm _ c hnabs hp.
have hnn := @measure_integral_negation R X mu hm _ c hn.
apply: (@measure_integral_graph_equivalent R X mu _ _ (-c) _ hnn).
exact: partial_extended_double_negation_graph.
Qed.
