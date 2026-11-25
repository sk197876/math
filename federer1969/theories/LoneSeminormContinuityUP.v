(** Federer (1969), 4.1.5, p. 350:
    continuity with respect to ||S||_(1).
    The epsilon-delta specification is on the
    original L1 partial functions; distance zero
    is allowed for distinct representatives. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureLpMembershipUP MeasureLpConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_lone_seminorm_continuous]: the original
    L1 seminorm continuity in Federer 4.1.5,
    p. 350, without passage to a chosen
    quotient representation. *)
Definition is_lone_seminorm_continuous (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (mu:set X->\bar R)
    (I:partial_function X (real_norm_metric_space hNY)->R):Prop:=
  forall f,is_measure_lp_function mu 1 f ->forall epsilon:R,0<epsilon ->
  exists delta:R,0<delta /\ forall g,is_measure_lp_function mu 1 g ->
    (measure_lp_distance mu NY 1 g f<delta%:E)%E ->`|I g-I f|<epsilon.
