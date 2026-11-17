(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(11), p. 334:
    a proper holomorphic subgerm has a strictly
    larger vanishing ideal. Apply the existing
    ideal separation theorem of 3.4.5; no
    dimension or stratification theorem is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP RealNormUP NormMetric HolomorphicGermRing SetGermUP SetGermOrder
  HolomorphicVarietyGermUP HolomorphicGermVanishingSealed HolomorphicGermVanishingMonotonicity HolomorphicVarietyGermSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_proper_subgerm_ideal_witness]:
    the strict ideal inclusion for alpha
    intersect beta in 3.4.12, p. 339, extending 3.4.8(11), p. 334. *)
Theorem holomorphic_proper_subgerm_ideal_witness (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @is_holomorphic_variety_germ R X NX hNX a beta ->
  set_germ_subset beta alpha ->alpha<>beta ->
  exists f:@holomorphic_germ_ring R X NX hNX a,
    @HolomorphicSetIdeal.value R X NX hNX a beta f /\
    ~@HolomorphicSetIdeal.value R X NX hNX a alpha f.
Proof.
move=>hBeta hSub hDifferent.
apply:contrapT=>hNoWitness.
have hIdeal:@HolomorphicSetIdeal.value R X NX hNX a beta `<=`
    @HolomorphicSetIdeal.value R X NX hNX a alpha.
  move=>f hf;apply:contrapT=>hNot;apply:hNoWitness;by exists f.
have hReverse:=@holomorphic_variety_germ_ideal_separation R X NX hNX a beta alpha hBeta hIdeal.
apply:hDifferent;exact:set_germ_subset_antisymmetric hReverse hSub.
Qed.
