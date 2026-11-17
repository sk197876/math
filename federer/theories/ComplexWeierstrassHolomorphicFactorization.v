(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: preparation
    reduces the original nonzero germ to a distinguished
    polynomial. Proved prime comparison restores a factorization
    in the whole analytic germ ring. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormDifferentialUP HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermUnits ComplexWeierstrassTransverseUP
  ComplexWeierstrassTransversePullback ComplexWeierstrassRegularUP ComplexWeierstrassPreparationUP
  ComplexWeierstrassPreparationExistence ComplexWeierstrassFunctionalPower
  CommutativeFactorizationUP CommutativeUnitLaws CommutativePolynomialSealed
  CommutativePolynomialEvaluationSealed HolomorphicPreparedPolynomialImage
  HolomorphicDistinguishedPolynomialFactorization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_holomorphic_prime_factorization]:
    the original dimension-induction step for factorization,
    3.4.7, p. 325. The actual transverse coefficient
    ring supplies the lower-dimensional induction premise.
    Preparation, polynomial coefficients, and analytic primes
    are proved conclusions, not additional hypotheses. *)
Theorem complex_weierstrass_holomorphic_prime_factorization (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (NK:K->R) (hNX:is_complex_norm NX) (hNK:is_complex_norm NK)
    (v:X) (xi:Hom X (ComplexScalars.C R)^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection)
    k (Phi:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0):
  @norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X)
    (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real xi) ->
  is_unique_factorization_commutative_domain
    [the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))] ->
  is_complex_weierstrass_regular_germ hNX Phi k v ->
  exists u:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0,
    exists F:seq (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0),
      is_commutative_unit u /\
      (forall p,p\in F ->is_commutative_prime_element p) /\
      Phi = u*\prod_(p<-F) p.
Proof.
move=>hXi hUFD hRegular.
pose A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
pose G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
pose E:=@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit.
have [fXi [hXiValues _]]:=@complex_weierstrass_functional_power_representative R X NX hNX xi 1 hXi.
have hXiActual x:holomorphic_representative_value fXi x = xi x by rewrite hXiValues expr1.
pose Gamma:G:=holomorphic_germ fXi.
pose B:=@CommutativePolynomial.space A.
pose embed:=@CommutativePolynomial.embed A.
pose variable:=@CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hP:=@CommutativePolynomial.laws A.
pose J:=@CommutativePolynomialEvaluation.map A B G embed variable coefficient hP E Gamma.
have hJ:=@CommutativePolynomialEvaluation.laws A B G embed variable coefficient hP E Gamma.
have [Q [W [Wi hPreparation]]]:=@complex_weierstrass_preparation_with_transverse_exists R X K NX NK hNX hNK
  v xi inclusion projection k Phi hSplit hXi hRegular.
have [P [hDistinguished hImage]]:=@holomorphic_prepared_polynomial_image R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXiActual B embed variable coefficient hP J hJ
  k W Wi (complex_weierstrass_preparation_polynomial hPreparation).
have [F [hPrimes hFactor]]:=@holomorphic_distinguished_polynomial_factorization R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiActual B embed variable coefficient hP J hJ
  hUFD P k hDistinguished.
have [q [hRepQ hValueQ]]:=complex_weierstrass_preparation_unit_value hPreparation.
have hUnitQ:is_commutative_unit Q.
  rewrite -hRepQ;exact:(@holomorphic_germ_unit_iff_nonzero_value R X NX (complex_norm_real hNX) 0 q).2 hValueQ.
have [u hInverse]:=hUnitQ.
exists u,F;split;first exact:commutative_inverse_unit hInverse.
split;first exact:hPrimes.
rewrite -hFactor hImage -(complex_weierstrass_preparation_identity hPreparation) mulrA hInverse mul1r.
reflexivity.
Qed.
