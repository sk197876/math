(** Federer (1969), 3.4.12, p. 339, extending the
    ideal-power argument of 3.4.8(5), p. 328: actual radial
    quotients lower the original vanishing order by one. Use
    their opaque derivative laws and the original contraction formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  SymmetricForms PolynomialTaylorTerms PolynomialTaylorTermContinuity ContinuousMultilinearUP ContinuousMultilinearSealed
  HolomorphicGermRing HolomorphicGermJetsSealed HolomorphicGermFormsUP HolomorphicGermFormsSealed
  HolomorphicRadialQuotientUP HolomorphicRadialQuotientSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [holomorphic_radial_quotient_zero_jet]: a zero
    successor derivative gives a zero quotient derivative, expanding
    Taylor's formula for 3.4.8(5), p. 328, under 3.4.12, p. 339. *)
Lemma holomorphic_radial_quotient_zero_jet (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) a
    (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a) v m:
  @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a m.+1 alpha=0 ->
  @HolomorphicGermJets.value R X NX (complex_norm_real hNX) a m
    (@HolomorphicRadialQuotient.map R X NX hNX a alpha v)=0.
Proof.
move=>hZero.
pose F:=@HolomorphicGermForms.value R X NX hNX a m.+1 alpha.
have hF:=@HolomorphicGermForms.laws R X NX hNX a m.+1 alpha.
have hForm:F=0 by apply:sform_ext=>u;rewrite hF hZero linear0 sform_zeroE.
apply:(continuous_multilinear_extensional (@ContinuousMultilinear.laws R m
  (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
  NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)))=>u.
rewrite (@HolomorphicRadialQuotient.laws R X NX hNX a alpha v m F hF u)
  hForm (symmetric_taylor_term_tuple_value (leqnSn m)) sform_zeroE !scaler0 linear0.
reflexivity.
Qed.

(** Source for [holomorphic_radial_quotient_lowers_order]: all original
    derivatives below k+1 vanishing force all quotient derivatives
    below k to vanish, supporting the complex ideal-power argument
    of 3.4.8(5), p. 328. *)
Lemma holomorphic_radial_quotient_lowers_order (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) a
    (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a) v k:
  (forall i,(i<k.+1)%N ->@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i alpha=0) ->
  forall i,(i<k)%N ->@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a i
    (@HolomorphicRadialQuotient.map R X NX hNX a alpha v)=0.
Proof.
move=>hZero i hi;apply:holomorphic_radial_quotient_zero_jet.
exact:hZero i.+1 hi.
Qed.
