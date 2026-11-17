(** Federer (1969), 3.4.7, p. 325: values at
    the origin detect units and specialize the transverse
    coefficients. The value map is specified by every
    actual representative before its existence is proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_analytic_germ_value_at_centre]: the
    original value at the centre is independent of
    the analytic representative, supporting units and coefficient
    specialization in 3.4.7, p. 325. *)
Definition is_analytic_germ_value_at_centre (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a
    (value:{rmorphism [the comNzRingType of (@analytic_germ_ring R X NX hNX a)]->R}):Prop:=
  forall f:@analytic_representative_type R X NX hNX a,
    value (analytic_germ f) = analytic_representative_value f a.
