(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(16), p. 337:
    var(ideal sigma) is the smallest holomorphic variety
    germ containing sigma. This is a consequence of
    the already proved ideal recovery and separation laws
    of 3.4.5, p. 320. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import FiniteCoordinates StandardHermitian StandardHermitian HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases HolomorphicCoordinateNorm HolomorphicLinear HolomorphicUP RealNormUP NormMetric HolomorphicGermRing SetGermUP SetGermOrder
  CommutativeIdealUP HolomorphicGermVanishingSealed HolomorphicGermVanishingMonotonicity HolomorphicVarietyGermUP
  HolomorphicVarietyGermSeparation HolomorphicIdealVarietyGermSealed HolomorphicIdealVarietyVanishingLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_hull_minimality]: the original minimality
    assertion in the first sentence of the proof
    of 3.4.8(16), p. 337. The source
    germ need not itself be holomorphic or measurable. *)
Theorem holomorphic_hull_minimality (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (sigma beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (hI:@is_finitely_generated_commutative_ideal [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]
      (@HolomorphicSetIdeal.value R X NX hNX a sigma)):
  @is_holomorphic_variety_germ R X NX hNX a beta ->set_germ_subset sigma beta ->
  set_germ_subset (@HolomorphicIdealVarietyGerm.value R X NX hNX a _ hI) beta.
Proof.
move=>hBeta hSub.
apply:(@holomorphic_variety_germ_ideal_separation R X NX hNX a beta _ hBeta).
rewrite (@HolomorphicIdealVarietyVanishingLaws.vanishing_ideal_variety_recovery R X NX hNX a sigma hI).
exact:(@holomorphic_set_ideal_antitone R X NX hNX a sigma beta hSub).
Qed.
