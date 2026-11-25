(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5), pp. 326, 328:
    actual analytic composition gives the pointed germ map.
    The existing opaque pullback supplies existence; no
    representation is exposed by the independent laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormAnalyticUP HolomorphicGermUP HolomorphicPullbackSealed
  HolomorphicPullbackRepresentative PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointed_holomorphic_germ_pullback_exists]: actual
    pointed analytic coordinate maps induce maps of their
    original germ spaces, supporting 3.4.8(1),(5), pp. 326, 328. *)
Theorem pointed_holomorphic_germ_pullback_exists (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:set X) (u:X->Y) (a:X) (b:Y):
  @is_holomorphic_at R X Y NX NY hNX hNY A u a ->u a=b ->
  exists P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a,
    is_pointed_holomorphic_germ_pullback u P.
Proof.
move=>hu <-.
exists (@HolomorphicPullback.map R X Y NX NY hNX hNY A u a hu)=>f.
exists (@holomorphic_pullback_representative R X Y NX NY hNX hNY A u a hu f).
split;first exact:(@HolomorphicPullback.laws R X Y NX NY hNX hNY A u a hu f).
by move=>x.
Qed.
