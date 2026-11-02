(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition
  ExtendedRealPartial MeasureUP MeasurePushforward MeasurableFunctionUP MeasureIntegralUP MeasureIntegral
  MeasureIntegralUniqueness MeasureIntegralPartsDifference PushforwardIntegralParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_pushforward_integral_iff]: the integral equality of
    Federer 2.4.18(1), p. 90, proof p. 91 Equality includes definedness:
    both integrals exist with the same value, or both are undefined when the
    two part integrals are infinite. No default is assigned to infinity
    minus infinity. *)
Theorem measure_pushforward_integral_iff (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> Y)
    (f : partial_function Y (extended_real_line R)) :
  is_measure_measurable_function mu (partial_function_precompose u f) -> forall a,
  is_measure_integral mu (partial_function_precompose u f) a <->
  is_measure_integral (measure_pushforward u mu) f a.
Proof.
move=> hf a.
have hpush := @measure_pushforward_is_measure R X Y u mu hm.
have [P [hpX hpY]] := @pushforward_positive_part_integrals R X Y mu hm u f hf.
have [N [hnX hnY]] := @pushforward_negative_part_integrals R X Y mu hm u f hf.
split=> hi.
- have [P' [N' [hp' [hn' hsub]]]] := (@measure_integral_parts_iff R X mu hm _ a).1 hi.
  have heP := measure_integral_unique hp' hpX.
  have heN := measure_integral_unique hn' hnX.
  rewrite heP heN in hsub.
  exact: (@measure_integral_from_parts R Y _ hpush f P N a hpY hnY hsub).
- have [P' [N' [hp' [hn' hsub]]]] := (@measure_integral_parts_iff R Y _ hpush f a).1 hi.
  have heP := measure_integral_unique hp' hpY.
  have heN := measure_integral_unique hn' hnY.
  rewrite heP heN in hsub.
  exact: (@measure_integral_from_parts R X mu hm _ P N a hpX hnX hsub).
Qed.

(** Source for [measure_pushforward_integrable_iff]: explicit
    definedness consequence of Federer 2.4.18(1), p. 90,
    as justified by the part-integral proof on p. 91. *)
Corollary measure_pushforward_integrable_iff (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> Y)
    (f : partial_function Y (extended_real_line R)) :
  is_measure_measurable_function mu (partial_function_precompose u f) ->
  is_measure_integrable mu (partial_function_precompose u f) <->
  is_measure_integrable (measure_pushforward u mu) f.
Proof.
move=> hf; split; move=> [a ha]; exists a.
- exact: (@measure_pushforward_integral_iff R X Y mu hm u f hf a).1 ha.
- exact: (@measure_pushforward_integral_iff R X Y mu hm u f hf a).2 ha.
Qed.

(** Source for [measure_pushforward_integral_value]: the displayed
    integral equality in Federer 2.4.18(1), p. 90,
    using public integral values after existence has been proved. *)
Corollary measure_pushforward_integral_value (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> Y)
    (f : partial_function Y (extended_real_line R))
    (hX : is_measure_integrable mu (partial_function_precompose u f))
    (hY : is_measure_integrable (measure_pushforward u mu) f) :
  measure_integral hX=measure_integral hY.
Proof.
have hiX := measure_integral_specification hX.
have hiY := (@measure_pushforward_integral_iff R X Y mu hm u f hiX.1 _).1 hiX.
exact: measure_integral_unique hiY (measure_integral_specification hY).
Qed.
