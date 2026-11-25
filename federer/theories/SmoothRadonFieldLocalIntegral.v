(** Federer (1969), 4.1.7, pp. 355–356:
    every original smooth field meets the
    local summability hypothesis of its Radon
    measurable-field extension. Reuse continuity
    on the original open subspace. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormClassZeroTopology NormRegularity
  SmoothFunctionSpaceUP CurrentMeasurableMultiplierUP ContinuousRadonFieldLocalIntegral
  MeasureUP RadonMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [smooth_radon_field_locally_summable]:
    a class-infinity field on U is locally
    norm-summable for every Radon measure on U,
    supporting Federer 4.1.7, pp. 355–356.
    No regularity near the boundary is imposed. *)
Theorem smooth_radon_field_locally_summable (R:realType) (X V:lmodType R)
    (NX:X->R) (NV:V->R) (hNX:is_real_norm NX) (hNV:is_real_norm NV)
    (U:set X) (E:lmodType R) (ev:E->X->V)
    (hE:is_smooth_function_space hNX hNV U ev)
    (mu:set (set_type (U:set (real_norm_metric_space hNX)))->\bar R)
    (hm:is_measure mu) (hr:is_radon_measure mu) (f:E):
  is_locally_summable_current_field hNV mu (fun x=>ev f (set_val x)).
Proof.
apply:(@continuous_radon_field_locally_summable R
  [the topologicalType of set_type (U:set (real_norm_metric_space hNX))]
  V NV hNV mu hm hr (fun x=>ev f (set_val x))).
apply:(@norm_class_zero_restriction_continuous R X V NX NV hNX hNV U (ev f)).
exact:(norm_class_continuous (smooth_function_evaluation_smooth hE f 0%N)).
Qed.
