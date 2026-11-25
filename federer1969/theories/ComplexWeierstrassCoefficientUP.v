(** Federer (1969), 3.4.12, p. 339, extending 3.4.6,
    pp. 322–323: specify the original complex mixed coefficients
    by their actual derivative values before proving existence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm SymmetricForms PolynomialTaylorTerms HomogeneousPolynomialFunctions
  ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicGermUP HolomorphicGermJetsSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_complex_weierstrass_split_coefficient]: the
    actual (i+j)th derivative, contracted with the original
    divided powers of v and the included transverse vector,
    3.4.12, p. 339, extending 3.4.6, p. 322. *)
Definition is_complex_weierstrass_split_coefficient (R:realType)
    (X K:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:is_complex_norm NX)
    (alpha:holomorphic_germ_space (complex_norm_real hNX) (0:X))
    (v:X) (inclusion:Hom K X) (i j:nat) (C:K->ComplexScalars.C R):Prop:=
  forall F:S_m X (ComplexScalars.C R)^o (i+j),
    (forall t,F t=@ContinuousMultilinear.evaluation R (i+j)%N
      (restricted_space (ComplexScalars.embed R) X)
      (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o)
      NX (@complex_modulus R) (complex_norm_real hNX) (@complex_modulus_real_norm R)
      [ffun s=>tnth t s]
      (@HolomorphicGermJets.value R X NX (complex_norm_real hNX) 0 (i+j)%N alpha)) ->
    forall z,C z=sform_polynomial_value (symmetric_taylor_term j F v) (inclusion z).

Arguments is_complex_weierstrass_split_coefficient {R X K NX} hNX alpha v inclusion i j C.
