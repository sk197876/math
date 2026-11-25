(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    actual analytic composition gives the pointed germ map.
    The existing opaque pullback supplies existence; no
    representation is exposed by the independent laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermUP AnalyticPullbackSealed
  AnalyticPullbackRepresentative PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointed_analytic_germ_pullback_exists]: actual
    pointed analytic coordinate maps induce maps of their
    original germ spaces, supporting 3.4.8(1),(5), pp. 326, 328. *)
Theorem pointed_analytic_germ_pullback_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (u:X->Y) (a:X) (b:Y):
  @norm_analytic_at R X Y NX NY hNX hNY A u a ->u a=b ->
  exists P:analytic_germ_space hNY b->analytic_germ_space hNX a,
    is_pointed_analytic_germ_pullback u P.
Proof.
move=>hu <-.
exists (@AnalyticPullback.map R X Y NX NY hNX hNY A u a hu)=>f.
exists (@analytic_pullback_representative R X Y NX NY hNX hNY A u a hu f).
split;first exact:(@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu f).
by move=>x.
Qed.
