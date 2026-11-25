(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5), pp. 326, 328:
    pointed analytic coordinate pullbacks are continuous for
    the original germ metric. Uniqueness transfers the proved
    analytic composition theorem to the independent pointed laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormAnalyticUP HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermMetric HolomorphicPullbackSealed HolomorphicPullbackRepresentative
  HolomorphicPullbackContinuity PointedHolomorphicPullbackUP PointedHolomorphicPullbackUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [pointed_holomorphic_germ_pullback_continuous]: the
    actual coordinate maps induce continuous maps of germs,
    supporting the original closed subrings and Borel
    assertions of 3.4.8(1),(5), pp. 326, 328. *)
Theorem pointed_holomorphic_germ_pullback_continuous (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:set X) (u:X->Y) (a:X) (b:Y)
    (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a):
  @is_holomorphic_at R X Y NX NY hNX hNY A u a ->u a=b ->
  is_pointed_holomorphic_germ_pullback u P ->
  continuous (fun alpha:@holomorphic_germ_metric R Y NY hNY b=>
    (P alpha:@holomorphic_germ_metric R X NX hNX a)).
Proof.
move=>hu hab hP;subst b.
pose Q:=@HolomorphicPullback.map R X Y NX NY hNX hNY A u a hu.
have hQ:is_pointed_holomorphic_germ_pullback u Q.
  move=>f;exists (@holomorphic_pullback_representative R X Y NX NY hNX hNY A u a hu f).
  split;first exact:(@HolomorphicPullback.laws R X Y NX NY hNX hNY A u a hu f).
  by move=>x.
have hEqual:P=Q.
  apply:funext=>alpha.
  exact:(@pointed_holomorphic_germ_pullback_unique R X Y NX NY hNX hNY a (u a) u P Q hP hQ alpha).
rewrite hEqual.
exact:(@holomorphic_germ_pullback_continuous R X Y NX NY hNX hNY A u a hu).
Qed.
