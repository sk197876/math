(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPrecomposition
  MeasureUP MeasurePushforward MeasureAlmostUP MeasureAlmostEquality MeasurableFunctionUP MeasurableAlmostModification
  PartialExtendedOrderLoci NonnegativeTotalRepresentative PushforwardMeasurableFunctions PushforwardAlmostEquality
  MeasureIntegralUP MeasureIntegralAlmostEquality PushforwardTotalNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pushforward_nonnegative_integrals]: the nonnegative case of
    Federer 2.4.18(1), pp. 90–91, retaining conull partial domains A common
    total nonnegative representative permits use of the characteristic
    expansion on both spaces with the same null changes. *)
Theorem pushforward_nonnegative_integrals (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> Y)
    (f : partial_function Y (extended_real_line R)) :
  is_measure_measurable_function mu (partial_function_precompose u f) ->
  measure_almost_everywhere (measure_pushforward u mu) (partial_extended_nonnegative_locus f) ->
  exists a, is_measure_integral mu (partial_function_precompose u f) a /\
    is_measure_integral (measure_pushforward u mu) f a.
Proof.
move=> hf hp.
have hpush := @measure_pushforward_is_measure R X Y u mu hm.
have hfY := @pushforward_function_measurable_from_composition R X Y (extended_real_line R) mu u f hf.
have [F [hpos [hFm hFe]]] := @measurable_nonnegative_total_representative R Y _ hpush f hfY hp.
have hFXe := @pushforward_almost_equal_precompose R X Y (extended_real_line R) mu u f (partial_function_total F) hFe.
have hFXm := @measurable_function_almost_equal R X (extended_real_line R) mu hm _ _ hf hFXe.
have [a [haX haY]] := @pushforward_total_nonnegative_integrals R X Y mu hm u F hpos hFXm.
exists a; split.
- exact: (@measure_integral_almost_equal R X mu hm _ _ a haX (measure_almost_equal_sym hFXe)).
- exact: (@measure_integral_almost_equal R Y _ hpush _ _ a haY (measure_almost_equal_sym hFe)).
Qed.
