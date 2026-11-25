(** Federer (1969), 4.1.5, p. 350:
    the integral pairing on every original L1
    partial function. This specification determines
    its values only on L1; it assigns no
    mathematical meaning outside that space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP MeasureLpMembershipUP
  MeasureIntegralUP AbstractDualPartialPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_dual_lone_integral]: the literal
    right-hand integral used to extend S in
    Federer 4.1.5, p. 350. Original partial
    domains are retained. *)
Definition is_dual_lone_integral (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (D:lmodType R) (ed:Hom D (Hom Y R^o)) (xi:X->D)
    (mu:set X->\bar R)
    (I:partial_function X (real_norm_metric_space hNY)->R):Prop:=
  forall f,is_measure_lp_function mu 1 f ->
    is_measure_integral mu (abstract_dual_partial_pairing ed xi f) (I f)%:E.
