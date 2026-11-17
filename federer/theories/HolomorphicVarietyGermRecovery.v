(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 320: an
    analytic variety germ with finitely generated ideal is
    recovered by the original ideal-to-variety operation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP NormMetric HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing
  SetGermUP SetGermLaws SetGermOrder CommutativeIdealUP HolomorphicGermVanishingSealed
  FiniteZeroSetSealed FiniteHolomorphicGermZeroSystem FiniteHolomorphicGermVanishingContainment
  HolomorphicVarietyGermUP HolomorphicVarietyGermRepresentatives HolomorphicVarietyGermSeparation HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyVanishingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_variety_germ_ideal_recovery]: the
    printed identity alpha=var(ideal alpha) under the original
    finite-generation hypothesis, 3.4.5, p. 320. *)
Theorem holomorphic_variety_germ_ideal_recovery (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (hI:@is_finitely_generated_commutative_ideal [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)] (@HolomorphicSetIdeal.value R X NX hNX a alpha)):
  @is_holomorphic_variety_germ R X NX hNX a alpha ->
  alpha=@HolomorphicIdealVarietyGerm.value R X NX hNX a _ hI.
Proof.
move=>hAlpha;apply:set_germ_subset_antisymmetric.
- exact:(@set_germ_in_variety_of_its_ideal R X NX hNX a alpha hI).
- apply:(@holomorphic_variety_germ_ideal_separation R X NX hNX a alpha _ hAlpha).
  exact:(@ideal_in_vanishing_ideal_of_variety R X NX hNX a _ hI).
Qed.
