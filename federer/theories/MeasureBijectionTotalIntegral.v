(** Total nonnegative integration under a measure-preserving bijection,
    supporting Federer (1969), 2.10.16, p. 178, by 2.4.18(1), pp. 90–91.
    Bijection laws transfer completed measurability on every set; no
    unjustified composition with a merely completed measurable function is
    used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasureBijectionUP MeasurePushforward
  PushforwardMeasurableSets PushforwardMeasurabilityTransfer PushforwardTotalNonnegativeIntegral MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_bijection_total_nonnegative_integral]:
    supporting actual integral transport for the rotations
    and coordinate permutations in 2.10.16, p. 178.
    This is the bijective case of 2.4.18(1), p. 90,
    with completed measurability justified by injectivity. *)
Theorem measure_bijection_total_nonnegative_integral (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu) (u : X -> Y) (ui : Y -> X)
    (f : Y -> extended_real_line R) a :
  is_measure_bijection mu nu u ui -> (forall y, 0<=f y) ->
  is_measure_integral nu (partial_function_total f) a ->
  is_measure_integral mu (partial_function_total (fun x => f (u x))) a.
Proof.
move=> hu hp hi.
have hf : is_measure_measurable_function mu (partial_function_total (fun x => f (u x))).
  constructor; first by rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
  move=> U hU; rewrite partial_function_total_preimage.
  have hmeas := measurable_function_open_preimage hi.1 hU.
  rewrite partial_function_total_preimage -(measure_bijection_pushforward hu) in hmeas.
  exact: measure_pushforward_preimage_measurable (can_inj (measure_bijection_cancel hu)) hmeas.
have [b [hb hc]] := pushforward_total_nonnegative_integrals hm hp hf.
rewrite (measure_bijection_pushforward hu) in hc.
by rewrite (measure_integral_unique hc hi) in hb.
Qed.
