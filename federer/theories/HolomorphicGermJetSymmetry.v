(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: actual
    germ derivatives are symmetric coefficients, by 3.1.11,
    p. 220. This supplies the reverse inclusion in the
    coefficient description of each growth class. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherDifferentialSymmetry FiniteArgumentPermutation
  HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermJetsUP HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_jet_symmetric]: each actual
    D^m(alpha) has the original permutation symmetry, as
    required for compactness in 3.4.5, p. 319. *)
Lemma holomorphic_germ_jet_symmetric (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a:X) m (alpha:holomorphic_germ_space hNX a)
    (sigma:'S_m) (u:{ffun 'I_m->X}):
  @ContinuousMultilinear.evaluation R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
    (finite_argument_permutation sigma u) (@HolomorphicGermJets.value R X NX hNX a m alpha)=
  @ContinuousMultilinear.evaluation R m (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
    u (@HolomorphicGermJets.value R X NX hNX a m alpha).
Proof.
have [f hf]:=@holomorphic_germ_has_representative R X NX hNX a alpha.
exact:(@norm_higher_differential_symmetric R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R)
  (fun i=>@ContinuousMultilinear.space R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))
  (fun i=>@ContinuousMultilinear.evaluation R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))
  (fun i=>@ContinuousMultilinear.norm R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))
  (fun i=>@ContinuousMultilinear.laws R i (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) hNX (@complex_modulus_real_norm R))
  setT _ m a _ (@HolomorphicGermJets.laws R X NX hNX a m alpha f hf) sigma u).
Qed.
