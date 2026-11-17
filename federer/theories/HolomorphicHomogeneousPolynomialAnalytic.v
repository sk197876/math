(** Federer (1969), 3.4.12, p. 339: the original
    complex homogeneous Taylor polynomials are holomorphic on the
    whole finite-dimensional source. Restrict their actual symmetric
    forms to the real field and reuse the proved polynomial calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP
  ComplexModulus ComplexScalarNorm ComplexScalarNormCompleteness ComplexOrderedBases HermitianUP
  HermitianRealImaginary HermitianComplexNorm InnerNorm HilbertFormCompactness LinearBasis
  SymmetricForms SymmetricFormSum SymmetricPolynomialEvaluation PolynomialFunctions HomogeneousPolynomialFunctions
  ComplexSymmetricFormRestriction ComplexSymmetricPolynomialRestriction ComplexSymmetricTaylorRestriction
  PolynomialTaylorTerms PolynomialDiagonalNorm FiniteInnerSymmetricFormBounds ContinuousSymmetricFormAdapter
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormAnalyticUP NormAnalyticPolynomial NormAnalyticOperations NormHigherDifferentialFirst
  HomogeneousPolynomialDifferentials NormDifferentialUP NormDifferentialLocal NormDifferentialDirectional NormOpenDomainLaws
  NormHigherDifferentialUP HolomorphicUP TensorFamilyUP FamilyUpdate MultilinearFamilyAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_homogeneous_polynomial_analytic]: every
    original complex homogeneous polynomial has its actual complex-linear
    first differential, supporting the leading polynomials of 3.4.11,
    p. 338, under 3.4.12, p. 339. Analyticity and
    derivative formulas follow from existing finite real polynomial calculus. *)
Theorem holomorphic_homogeneous_polynomial_analytic (R:realType)
    (X:lmodType (ComplexScalars.C R)) (H:X->X->ComplexScalars.C R)
    (hH:is_hermitian_product H) n (e:'I_n->X) (he:is_basis e) k
    (F:S_m X (ComplexScalars.C R)^o k):
  let NX:=inner_norm (hermitian_real_inner_product hH) in
  let hNX:=complex_norm_real (hermitian_complex_norm hH) in
  @is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
    (@complex_modulus_real_norm R) setT (sform_polynomial_value F).
Proof.
move=>NX hNX.
pose XR:=restricted_space (ComplexScalars.embed R) X.
pose CR:=restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o.
pose NC:=@complex_modulus R;pose hNC:=@complex_modulus_real_norm R.
have [G hG]:=@complex_symmetric_form_real_exists R X (ComplexScalars.C R)^o k F.
have hGBound:@norm_bounded_symmetric_form R k XR CR NX NC G.
  exact:(@finite_inner_symmetric_form_bounded R XR CR (hermitian_real_part H)
    (hermitian_real_inner_product hH) NC hNC.1 (n+n)
    (ordered_real_basis e) (ordered_real_basisP he) k G).
pose P:=polynomial_from_forms (sform_include G).
have hValue:(fun x:X=>P x)=sform_polynomial_value F.
  apply:funext=>x;rewrite /P polynomial_from_formsE symmetric_polynomial_value_include.
  exact:complex_symmetric_polynomial_real_value hG x.
have hAnalytic:@norm_analytic R XR CR NX NC hNX hNC setT P.
  apply:(@norm_polynomial_function_analytic R XR CR NX NC hNX hNC
    (@complex_scalar_norm_complete R) P)=>i _.
  exact:(@finite_inner_symmetric_form_bounded R XR CR (hermitian_real_part H)
    (hermitian_real_inner_product hH) NC hNC.1 (n+n)
    (ordered_real_basis e) (ordered_real_basisP he) i _).
split;first by rewrite -hValue.
pose Z i:=@ContinuousMultilinear.space R i XR CR NX NC hNX hNC.
pose ev i:=@ContinuousMultilinear.evaluation R i XR CR NX NC hNX hNC.
pose NZ i:=@ContinuousMultilinear.norm R i XR CR NX NC hNX hNC.
pose hZ i:=@ContinuousMultilinear.laws R i XR CR NX NC hNX hNC.
have [D [hEval [hActual hContinuity]]]:=@homogeneous_polynomial_differential_fields R XR CR
  NX NC hNX hNC Z ev NZ hZ setT (fun x _=>@norm_full_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX x) k G hGBound.
move=>a L ha hL.
have hFirst:=(@norm_higher_differential_first R XR CR NX NC hNX hNC Z ev NZ hZ
  setT (sform_polynomial_value G) a (D 1%N a)).1 (hActual 1%N a ha).
have hSame:sform_polynomial_value G=sform_polynomial_value F.
  apply:funext=>x;exact:complex_symmetric_polynomial_real_value hG x.
rewrite hSame in hFirst.
have hEqual:=norm_differential_unique hNX hNC hL hFirst.
move=>c v;rewrite hEqual.
change (ev 1%N [ffun _=>c*:(v:X)] (D 1%N a)=c*:(ev 1%N [ffun _=>v] (D 1%N a):(ComplexScalars.C R)^o)).
rewrite !hEval !(complex_symmetric_taylor_restriction hG).
have hScalar:=@multilinear_family_scale (ComplexScalars.C R) 1%N (fun _=>X) (ComplexScalars.C R)^o
  (fun u=>symmetric_taylor_term 1%N F a [tuple u l|l<1])
  (sform_finite_family_multilinear (symmetric_taylor_term 1%N F a))
  [ffun _=>0] ord0 c v.
by rewrite !one_arity_replace in hScalar.
Qed.
