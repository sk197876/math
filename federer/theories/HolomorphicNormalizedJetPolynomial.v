(** Federer (1969), 3.4.12, p. 339: the actual complex
    derivative supplies its original factorial-normalized homogeneous
    polynomial. Reuse the sealed complex form, original polynomial
    evaluation and exact scalar-restriction equation already proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus
  ComplexScalarNorm HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm HilbertFormCompactness
  LinearBasis SymmetricForms SymmetricFormSum SymmetricPolynomialEvaluation PolynomialFunctions
  HomogeneousPolynomialFunctions ContinuousMultilinearUP ContinuousMultilinearSealed HolomorphicUP
  HolomorphicGermUP HolomorphicGermFormsSealed HolomorphicGermJetsSealed
  HolomorphicGermDirectionalCoefficient HolomorphicHomogeneousPolynomialAnalytic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_normalized_jet_polynomial_exists]: the
    original polynomial corresponding to D^k Phi(0), extending
    3.4.11, p. 338, under 3.4.12, p. 339. Its complex
    polynomial and analytic laws are proved from the original actual
    jet, including degree and ambient dimension zero. *)
Theorem holomorphic_normalized_jet_polynomial_exists (R:realType)
    (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
    (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e) k
    (alpha:holomorphic_germ_space (complex_norm_real (hermitian_complex_norm hH)) (0:X)):
  let NX:=inner_norm (hermitian_real_inner_product hH) in
  let hNX:=complex_norm_real (hermitian_complex_norm hH) in
  exists P:PolynomialFunction X (ComplexScalars.C R)^o,
    @is_homogeneous_polynomial (ComplexScalars.C R) X (ComplexScalars.C R)^o k P /\
    @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
      (@complex_modulus_real_norm R) setT P /\
    forall v,P v=((k`!)%:R:R)^-1*:
      (@ContinuousMultilinear.evaluation R k (restricted_space (ComplexScalars.embed R) X)
        (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R)
        hNX (@complex_modulus_real_norm R) [ffun _=>v] (@HolomorphicGermJets.value R X NX hNX 0 k alpha)).
Proof.
move=>NX hNX.
pose F:=@HolomorphicGermForms.value R X NX (hermitian_complex_norm hH) 0 k alpha.
pose P:=polynomial_from_forms (sform_include F).
have hValue v:P v=sform_polynomial_value F v.
  by rewrite /P polynomial_from_formsE symmetric_polynomial_value_include.
exists P;split;first by exists F.
split.
- have hHOL:=@holomorphic_homogeneous_polynomial_analytic R X H hH n e he k F.
  have hFunctions:(fun x:X=>P x)=sform_polynomial_value F by apply:funext=>x;exact:hValue.
  rewrite -hFunctions in hHOL;exact:hHOL.
- move=>v;rewrite hValue.
  exact:(@holomorphic_germ_directional_coefficient_real_value R X NX (hermitian_complex_norm hH) 0 k alpha v).
Qed.
