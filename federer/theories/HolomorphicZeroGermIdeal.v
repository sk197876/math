(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: membership
    in the ideal of a set germ is exactly containment
    in the original zero variety germ of the function. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws
  SetGermUP SetGermLaws SetGermOrder HolomorphicGermVanishingUP HolomorphicGermVanishingSealed HolomorphicGermVanishingRepresentative
  HolomorphicZeroGermUP HolomorphicZeroGermSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_zero_germ_ideal_equivalence]: the
    original local-vanishing definition is equivalent to set
    germ containment, supporting irreducibility in 3.4.5, p. 320. *)
Theorem holomorphic_zero_germ_ideal_equivalence (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (alpha:holomorphic_germ_space hNX a):
  @HolomorphicSetIdeal.value R X NX hNX a sigma alpha <->
  set_germ_subset sigma (@HolomorphicZeroGerm.value R X NX hNX a alpha).
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [S <-]:=@set_germ_has_representative T a sigma.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
rewrite -hf (holomorphic_set_ideal_representative_equation f S)
  -(@HolomorphicZeroGerm.laws R X NX hNX a (holomorphic_germ f) f (erefl _))
  set_germ_subset_original.
by [].
Qed.
