(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: subtraction
    of original germs commutes with every actual derivative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP HolomorphicGermUP HolomorphicGermSealed HolomorphicGermRing
  ContinuousMultilinearSealed HolomorphicGermJetsSealed HolomorphicGermJetArithmetic HolomorphicGermJetZeroNegate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_jet_difference]: actual
    derivative subtraction for the metric and continuous
    operations in 3.4.5, p. 319. *)
Lemma holomorphic_germ_jet_difference (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) m
    (alpha beta:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]):
  @HolomorphicGermJets.value R X NX hNX a m (alpha-beta)=
    @HolomorphicGermJets.value R X NX hNX a m alpha-@HolomorphicGermJets.value R X NX hNX a m beta.
Proof.
change (@HolomorphicGermJets.value R X NX hNX a m
  (@HolomorphicGerms.add R X NX hNX a alpha (@HolomorphicGerms.opp R X NX hNX a beta))=
  @HolomorphicGermJets.value R X NX hNX a m alpha-@HolomorphicGermJets.value R X NX hNX a m beta).
by rewrite holomorphic_germ_jet_add holomorphic_germ_jet_negate.
Qed.
