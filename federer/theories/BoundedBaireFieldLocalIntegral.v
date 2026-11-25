(** Federer (1969), 4.1.7, p. 359:
    every bounded Baire field is locally
    norm-summable for the original Radon measure.
    The Baire-to-Borel inclusion is 2.2.15,
    p. 70; compact finiteness and the
    earlier norm domination give the integral. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric BaireFunctions BaireBorel BorelFunctionBasic
  PartialFunctionBasic MeasureUP RadonMeasureUP MeasurableFunctionUP MeasurableIdentityCriterion
  MeasurableTotalBasic CurrentMeasurableMultiplierUP MeasurableCompactNormIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [bounded_baire_field_locally_summable]:
    bounded Baire fields satisfy every local
    summability condition for the original measurable
    current products, supporting Federer 4.1.7,
    p. 359. Total mass finiteness and
    compact support of the field are unnecessary. *)
Theorem bounded_baire_field_locally_summable (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (f:X->Y) (M:R):
  @is_baire_function R X (real_norm_metric_space hNY) f->
  0<=M->(forall x,NY (f x)<=M)->is_locally_summable_current_field hNY mu f.
Proof.
move=>hF hM hBound.
have hIdentity:=(@measurable_identity_iff_open_sets R X mu hm).2 (radon_open_measurable hr).
have hMeas:=@measurable_total_borel_postcomposition R X X (real_norm_metric_space hNY)
  mu hm id f hIdentity (baire_function_borel hF).
split;first exact:hMeas.
move=>K hK;exact:(@measurable_compact_norm_integral R X Y NY hNY mu hm hr f K M
  hMeas hK hM (fun x _=>hBound x)).
Qed.
