(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPrecomposition MeasureUP MeasureAlmostUP
  MeasurePushforward PushforwardMeasurableSets RegularMeasureUP RegularMeasurePushforward MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pushforward_function_measurable_from_composition]: first
    conclusion of Federer 2.4.18(1), p. 90, proof p. 91 The composition's
    conull domain also gives the required target conull domain, so it need
    not be assumed separately. *)
Theorem pushforward_function_measurable_from_composition (R : realType)
    (X Y : choiceType) (Z : topologicalType) (mu : set X -> \bar R)
    (u : X -> Y) (f : partial_function Y Z) :
  is_measure_measurable_function mu (partial_function_precompose u f) ->
  is_measure_measurable_function (measure_pushforward u mu) f.
Proof.
move=> hf; constructor.
- have hd := measurable_function_domain hf.
  by rewrite /measure_almost_everywhere /measure_pushforward preimage_setC.
- move=> U hU; apply: (@pushforward_measurable_from_preimage R X Y mu u (partial_function_preimage f U)).
  exact: (measurable_function_open_preimage hf hU).
Qed.

(** Source for [regular_pushforward_measurable_composition]: Federer
    2.4.18(2), p. 90, proof p. 91, by 2.1.5(4). The stronger arbitrary
    topological target follows from the identical open-inverse-image
    argument. *)
Theorem regular_pushforward_measurable_composition (R : realType)
    (X Y : choiceType) (Z : topologicalType) (mu : set X -> \bar R)
    (hm : is_measure mu) (hr : is_regular_measure mu)
    (u : X -> Y) (f : partial_function Y Z) :
  mu setT < +oo -> is_measure_measurable_function (measure_pushforward u mu) f ->
  is_measure_measurable_function mu (partial_function_precompose u f).
Proof.
move=> hfin hf; constructor.
- have hd := measurable_function_domain hf.
  by rewrite /measure_almost_everywhere /measure_pushforward preimage_setC in hd.
- move=> U hU; rewrite partial_function_precompose_preimage.
  exact: (@regular_measure_pushforward_measurable_preimage R X Y mu hm hr u _ hfin
    (measurable_function_open_preimage hf hU)).
Qed.
