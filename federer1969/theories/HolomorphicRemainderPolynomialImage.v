(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: actual analytic
    division remainders are finite transverse polynomials.
    The independently proved bounded polynomial-image module
    and original remainder theorem prove this assertion;
    polynomial membership is not an additional hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormDifferentialUP HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermRing ComplexWeierstrassTransverseUP ComplexWeierstrassTransversePullback
  ComplexWeierstrassDivisionUP ComplexWeierstrassRemainderModule CommutativePolynomialUP
  CommutativePolynomialEvaluationUP PolynomialBoundedEvaluationModule RingScalarRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RemainderImage.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
Local Notation E:=(@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(holomorphic_germ fXi:G).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.

(** Source for [holomorphic_directional_remainder_polynomial_image]:
    every actual remainder of directional order below k
    lies in the original polynomial subring, with every
    coefficient of degree at least k zero, supporting
    the factor argument in 3.4.7, p. 325. *)
Theorem holomorphic_directional_remainder_polynomial_image k (rho:G):
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  (forall x,holomorphic_representative_value fXi x = xi x) ->
  @is_complex_directional_polynomial_germ R X NX (complex_norm_real hNX) k v rho ->
  exists P:B,(forall i,(k<=i)%N ->coefficient P i = 0) /\rho = J P.
Proof.
move=>hXi hXiValues hRemainder.
have hModule:=@bounded_polynomial_image_submodule A B G embed variable coefficient
  hP E Gamma J hJ k.
have hGenerators i (hi:(i<k)%N):exists P:B,
    (forall j,(k<=j)%N ->coefficient P j = 0) /\Gamma^+i = J P.
  exact:(@bounded_polynomial_image_contains_power A B G embed variable coefficient
    hP E Gamma J hJ k i hi).
exact:(@complex_weierstrass_remainder_in_transverse_module R X K NX NK hNX hNK
  v xi inclusion projection hSplit k fXi
  (fun x=>exists P:B,(forall i,(k<=i)%N ->coefficient P i = 0) /\x = J P)
  rho hXi hXiValues hModule hGenerators hRemainder).
Qed.
End RemainderImage.
