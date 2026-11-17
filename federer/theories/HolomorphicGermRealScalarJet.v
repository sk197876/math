(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 319: multiplication by a real constant embedded in
    the original complex field scales every actual real jet.
    Use the already proved complex scalar form equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm SymmetricForms ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  ComplexWeierstrassScalarGermArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_germ_real_scalar_jet]: the actual
    finite-jet scalar law, supporting closed ideals in the
    complex extension, 3.4.12, p. 339. *)
Lemma holomorphic_germ_real_scalar_jet (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) a m (c:R)
    (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a):
  @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a m
    ((holomorphic_germ (@holomorphic_constant_representative R X NX (complex_norm_real hNX) a
      (ComplexScalars.embed R c)):@holomorphic_germ_ring R X NX (complex_norm_real hNX) a)*alpha) =
    c*:@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a m alpha.
Proof.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R m XR CR NX (@complex_modulus R)
  (complex_norm_real hNX) (@complex_modulus_real_norm R)))=>u.
rewrite linearZ /=.
have hTuple:[ffun i=>tnth [tuple u j|j<m] i]=u
  by apply/ffunP=>i;rewrite ffunE tnth_mktuple.
have hEval beta:@ContinuousMultilinear.evaluation R m XR CR NX (@complex_modulus R)
    (complex_norm_real hNX) (@complex_modulus_real_norm R) u
    (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a m beta)=
    (@HolomorphicGermForms.value R X NX hNX a m beta) [tuple u j|j<m].
  by rewrite (@HolomorphicGermForms.laws R X NX hNX a m beta) hTuple.
rewrite !hEval complex_weierstrass_scalar_germ_form sform_scaleE.
reflexivity.
Qed.
