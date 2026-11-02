(** Federer (1969), 2.4.10, p. 85: measurable sets split the density measure
    even when the density itself is not measurable. The essential supporting
    inequality is obtained by restricting each upper step function to the
    two measurable pieces. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP
  PartialZeroExtension PartialZeroExtensionSplit MeasureUP MeasureAlmostUP MeasureFiniteClosure
  PartialExtendedOrderLoci MeasureStepFunctionUP MeasureStepNonnegative MeasureZeroStepFunction
  MeasureUpperZeroExtension MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureStepIntegralIdentification MeasureIntegralAddition MeasureIntegralGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_nonnegative_step_split]: supporting
    additive splitting of an almost-everywhere nonnegative step
    function in Federer 2.4.10, p. 85. Infinite
    assigned values are permitted, since both pieces are nonnegative. *)
Lemma measure_nonnegative_step_split (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (u : partial_function X (real_line_metric R)) a :
  measure_measurable mu A -> is_measure_step_function mu u ->
  measure_almost_everywhere mu (partial_real_nonnegative_locus u) -> is_measure_step_integral mu u a ->
  exists b c, is_measure_step_integral mu (partial_function_zero_extension (0%R : real_line_metric R) A u) b /\
    is_measure_step_integral mu (partial_function_zero_extension (0%R : real_line_metric R) (~` A) u) c /\
    0 <= b /\ 0 <= c /\ b+c=a.
Proof.
move=> hA hu hp ha.
have hAc := measure_measurable_complement hA.
have hv := @measure_step_zero_extension R X mu hm A u hA hu.
have hw := @measure_step_zero_extension R X mu hm (~` A) u hAc hu.
have [b hb] := step_function_sum_defined hv.
have [c hc] := step_function_sum_defined hw.
have hbp := @measure_step_integral_nonnegative R X mu hm _ b
  (@zero_extension_real_nonnegative_almost R X mu hm A u hp) hb.
have hcp := @measure_step_integral_nonnegative R X mu hm _ c
  (@zero_extension_real_nonnegative_almost R X mu hm (~` A) u hp) hc.
have hbi := @measure_step_function_integral R X mu hm _ b hv hb.
have hci := @measure_step_function_integral R X mu hm _ c hw hc.
have hbi' := @measure_integral_graph_equivalent R X mu _ _ b
  (zero_extension_real_embedding_graph A u) hbi.
have hci' := @measure_integral_graph_equivalent R X mu _ _ c
  (zero_extension_real_embedding_graph (~` A) u) hci.
have hsum : extended_add b c=Some (b+c) by rewrite /extended_add ge0_adde_def.
have hboth := @measure_integral_add R X mu hm _ _ b c (b+c) hbi' hci' hsum.
have hwhole := @measure_integral_graph_equivalent R X mu _ _ (b+c)
  (partial_zero_extension_split_graph A (partial_real_function_embed u)) hboth.
have hai := @measure_step_function_integral R X mu hm u a hu ha.
have he := measure_integral_unique hwhole hai.
exists b,c; by split=> //; split=> //; split=> //; split.
Qed.

(** Source for [measure_nonnegative_upper_split_lower_bound]:
    the splitting inequality needed for measurability of a
    set under the density measure in Federer 2.4.10,
    p. 85. The function f is only assumed
    nonnegative almost everywhere, not measurable. *)
Lemma measure_nonnegative_upper_split_lower_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) :
  measure_measurable mu A -> measure_almost_everywhere mu (partial_extended_nonnegative_locus f) ->
  measure_upper_integral mu (partial_function_zero_extension (0 : extended_real_line R) A f) +
  measure_upper_integral mu (partial_function_zero_extension (0 : extended_real_line R) (~` A) f) <=
  measure_upper_integral mu f.
Proof.
move=> hA hp; apply: (measure_upper_integral_specification mu f).2=> a [u [hu ha]].
have hup := @nonnegative_upper_step_nonnegative_almost R X mu hm f u hp hu.
have [b [c [hb [hc [hbp [hcp he]]]]]] := @measure_nonnegative_step_split R X mu hm A u a hA hu.1 hup ha.
rewrite -he; apply: leeD.
- apply: (@measure_upper_integral_bound R X mu _ _ b _ hb).
  exact (@measure_upper_step_zero_extension R X mu hm A f u hA hu).
- apply: (@measure_upper_integral_bound R X mu _ _ c _ hc).
  exact (@measure_upper_step_zero_extension R X mu hm (~` A) f u (measure_measurable_complement hA) hu).
Qed.
