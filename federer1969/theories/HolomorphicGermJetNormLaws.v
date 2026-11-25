(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the
    actual derivative-coordinate seminorm laws used in the
    original germ metric and continuity of ring operations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermOperationsUP RealNormUP HolomorphicGermUP HolomorphicGermRing
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  HolomorphicGermJetsSealed HolomorphicGermGrowthUP HolomorphicGermJetArithmetic HolomorphicGermJetDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_jet_norm_nonnegative]: each
    actual derivative norm is nonnegative, 3.4.5, p. 319. *)
Lemma holomorphic_germ_jet_norm_nonnegative (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) m (alpha:holomorphic_germ_space hNX a):
  0<=@holomorphic_germ_jet_norm R X NX hNX a m alpha.
Proof.
exact:(real_seminorm_nonnegative
  (continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
    (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))).1 _).
Qed.

(** Source for [holomorphic_germ_jet_norm_add]: the actual
    derivative norm satisfies the sum inequality on original
    germs, supporting 3.4.5, p. 319. *)
Lemma holomorphic_germ_jet_norm_add (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) m
    (alpha beta:[the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]):
  @holomorphic_germ_jet_norm R X NX hNX a m (alpha+beta)<=
    @holomorphic_germ_jet_norm R X NX hNX a m alpha+@holomorphic_germ_jet_norm R X NX hNX a m beta.
Proof.
rewrite /holomorphic_germ_jet_norm holomorphic_germ_jet_add.
exact:(real_seminorm_triangle
  (continuous_multilinear_norm_is_norm (@complex_modulus_real_norm R)
    (@ContinuousMultilinear.laws R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))).1 _ _).
Qed.
