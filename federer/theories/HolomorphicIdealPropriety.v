(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: a
    set-germ ideal is proper exactly when the original set
    germ is nonempty. This exposes the empty-germ convention
    in the printed irreducibility/prime-ideal assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermUP HolomorphicGermRing SetGermUP SetGermOrder SetGermBoundary
  HolomorphicGermVanishingSealed HolomorphicZeroGermIdeal HolomorphicZeroGermLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_set_ideal_contains_one]: the unit
    vanishes locally on S exactly when S has empty
    germ, supporting 3.4.5, p. 320. *)
Lemma holomorphic_set_ideal_contains_one (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  @HolomorphicSetIdeal.value R X NX hNX a sigma (@holomorphic_germ_one R X NX hNX a) <->
  sigma=@set_germ (Topological.clone (real_norm_metric_space hNX) _) a set0.
Proof.
rewrite holomorphic_zero_germ_ideal_equivalence holomorphic_zero_germ_one;split.
- exact:set_germ_subset_empty.
- move=>->;exact:set_germ_subset_reflexive.
Qed.
