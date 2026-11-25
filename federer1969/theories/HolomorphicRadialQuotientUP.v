(** Federer (1969), 3.4.12, p. 339, extending the
    ideal-closedness proof of 3.4.8(5), p. 328: specify
    radial quotient germs by their actual original derivative
    equations before proving existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm
  SymmetricForms PolynomialTaylorTerms ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermRing
  HolomorphicGermJetsSealed HolomorphicGermFormsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_holomorphic_radial_quotient]: its mth actual
    derivative is the contraction of the original (m+1)st
    derivative with v, divided by m+1. This expands Taylor's
    formula, 3.1.24, pp. 238–239, in the complex local ring
    of 3.4.12, p. 339. No quotient existence is assumed. *)
Definition is_holomorphic_radial_quotient (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) a
    (alpha:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a) (v:X)
    (q:@holomorphic_germ_ring R X NX (complex_norm_real hNX) a):Prop:=
  forall m (F:S_m X (ComplexScalars.C R)^o m.+1),
    @is_holomorphic_germ_form R X NX hNX a m.+1 alpha F ->
    forall u,@ContinuousMultilinear.evaluation R m (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R)
      (complex_norm_real hNX) (@complex_modulus_real_norm R) u
      (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) a m q)=
      (((m.+1)%:R:ComplexScalars.C R)^-1*:symmetric_taylor_term m F v [tuple u i|i<m]).
