(** Federer (1969), 3.4.5, p. 319: the map on
    original analytic germs is specified by all representative
    equations before its existence or selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticPullbackRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_analytic_germ_pullback]: the displayed
    representative equation for the induced map in 3.4.5,
    p. 319, required for every original analytic representative. *)
Definition is_analytic_germ_pullback (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (u:X->Y) (a:X)
    (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a)
    (P:analytic_germ_space hNY (u a)->analytic_germ_space hNX a):Prop:=
  forall f:@analytic_representative_type R Y NY hNY (u a),
    P (analytic_germ f)=analytic_germ (@analytic_pullback_representative R X Y NX NY hNX hNY A u a hu f).
