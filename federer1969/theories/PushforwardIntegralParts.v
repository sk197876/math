(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition
  ExtendedRealPartial PartialFunctionIntegralParts MeasureUpperIntegralPositivePart
  MeasureUP MeasurePushforward MeasurableFunctionUP MeasurableExtendedParts MeasurableGraphEquivalence
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralPartsExist
  PushforwardMeasurableFunctions PushforwardNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pushforward_positive_part_integrals]: the positive part in
    the final case of Federer 2.4.18(1), proof p. 91 Positive part commutes
    with composition at the graph level. *)
Lemma pushforward_positive_part_integrals (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> Y)
    (f : partial_function Y (extended_real_line R)) :
  is_measure_measurable_function mu (partial_function_precompose u f) -> exists a,
  is_measure_integral mu (partial_extended_function_positive_part (partial_function_precompose u f)) a /\
  is_measure_integral (measure_pushforward u mu) (partial_extended_function_positive_part f) a.
Proof.
move=> hf.
have hpush := @measure_pushforward_is_measure R X Y u mu hm.
have hfY := @pushforward_function_measurable_from_composition R X Y (extended_real_line R) mu u f hf.
have hp := @measurable_extended_positive_part R X mu hm _ hf.
have hp' : is_measure_measurable_function mu
    (partial_function_precompose u (partial_extended_function_positive_part f)).
  exact: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _
    (fun x z => iff_refl _) hp).
have hnon := (@partial_parts_nonnegative_almost R Y _ hpush f (measurable_function_domain hfY)).1.
have [a [ha hb]] := @pushforward_nonnegative_integrals R X Y mu hm u _ hp' hnon.
exists a; split=> //.
Qed.

(** Source for [pushforward_negative_part_integrals]: the negative part in
    Federer 2.4.18(1), proof p. 91 *)
Lemma pushforward_negative_part_integrals (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> Y)
    (f : partial_function Y (extended_real_line R)) :
  is_measure_measurable_function mu (partial_function_precompose u f) -> exists a,
  is_measure_integral mu (partial_extended_function_negative_part (partial_function_precompose u f)) a /\
  is_measure_integral (measure_pushforward u mu) (partial_extended_function_negative_part f) a.
Proof.
move=> hf.
have hpush := @measure_pushforward_is_measure R X Y u mu hm.
have hfY := @pushforward_function_measurable_from_composition R X Y (extended_real_line R) mu u f hf.
have hp := @measurable_extended_negative_part R X mu hm _ hf.
have hp' : is_measure_measurable_function mu
    (partial_function_precompose u (partial_extended_function_negative_part f)).
  exact: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _
    (fun x z => iff_refl _) hp).
have hnon := (@partial_parts_nonnegative_almost R Y _ hpush f (measurable_function_domain hfY)).2.
have [a [ha hb]] := @pushforward_nonnegative_integrals R X Y mu hm u _ hp' hnon.
exists a; split=> //.
Qed.
