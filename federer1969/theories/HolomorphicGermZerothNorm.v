(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the zeroth
    derivative of a germ is the value of any original
    representative at its centre. Its norm is the absolute value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicAtUP HolomorphicAtAnalytic HolomorphicGermAnalytic RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearZero NormHigherDifferentialUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermJetsUP HolomorphicGermJetsSealed HolomorphicGermGrowthUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_zeroth_norm]: the m=0
    term of the original germ metric, 3.4.5, p. 319,
    retains the actual function value. *)
Lemma holomorphic_germ_zeroth_norm (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X)
    (alpha:holomorphic_germ_space hNX a) (f:@holomorphic_representative_type R X NX hNX a):
  holomorphic_germ f=alpha ->@holomorphic_germ_jet_norm R X NX hNX a 0%N alpha=
    complex_modulus (holomorphic_representative_value f a).
Proof.
move=>hf.
have hActual:=@HolomorphicGermJets.laws R X NX hNX a 0%N alpha f hf.
rewrite /holomorphic_germ_jet_norm
  (continuous_multilinear_zero_norm (@complex_modulus_real_norm R)
    (@ContinuousMultilinear.laws R 0%N (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))).
by rewrite hActual.2.
Qed.
