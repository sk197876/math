(** Federer (1969), 3.4.7, p. 325: preparation
    reduces the original nonzero germ to a distinguished
    polynomial. Proved prime comparison restores a factorization
    in the whole analytic germ ring. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermUnits WeierstrassTransverseUP
  WeierstrassTransversePullback WeierstrassRegularUP WeierstrassPreparationUP
  WeierstrassPreparationExistence WeierstrassFunctionalPower
  CommutativeFactorizationUP CommutativeUnitLaws CommutativePolynomialSealed
  CommutativePolynomialEvaluationSealed AnalyticPreparedPolynomialImage
  AnalyticDistinguishedPolynomialFactorization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_analytic_prime_factorization]:
    the original dimension-induction step for factorization,
    3.4.7, p. 325. The actual transverse coefficient
    ring supplies the lower-dimensional induction premise.
    Preparation, polynomial coefficients, and analytic primes
    are proved conclusions, not additional hypotheses. *)
Theorem weierstrass_analytic_prime_factorization (R:realType) (X K:lmodType R)
    (NX:X->R) (NK:K->R) (hNX:is_real_norm NX) (hNK:is_real_norm NK)
    (v:X) (xi:Hom X R^o) (inclusion:Hom K X) (projection:Hom X K)
    (hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection)
    k (Phi:@analytic_germ_ring R X NX hNX 0):
  norm_bounded_linear NX (fun t:R^o=>`|t|) xi ->
  is_unique_factorization_commutative_domain
    [the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))] ->
  is_weierstrass_regular_germ Phi k v ->
  exists u:@analytic_germ_ring R X NX hNX 0,
    exists F:seq (@analytic_germ_ring R X NX hNX 0),
      is_commutative_unit u /\
      (forall p,p\in F ->is_commutative_prime_element p) /\
      Phi = u*\prod_(p<-F) p.
Proof.
move=>hXi hUFD hRegular.
pose A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose E:=@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit.
have [fXi [hXiValues _]]:=@weierstrass_functional_power_representative R X NX hNX xi 1 hXi.
have hXiActual x:analytic_representative_value fXi x = xi x by rewrite hXiValues expr1.
pose Gamma:G:=analytic_germ fXi.
pose B:=@CommutativePolynomial.space A.
pose embed:=@CommutativePolynomial.embed A.
pose variable:=@CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hP:=@CommutativePolynomial.laws A.
pose J:=@CommutativePolynomialEvaluation.map A B G embed variable coefficient hP E Gamma.
have hJ:=@CommutativePolynomialEvaluation.laws A B G embed variable coefficient hP E Gamma.
have [Q [W [Wi hPreparation]]]:=@weierstrass_preparation_with_transverse_exists R X K NX NK hNX hNK
  v xi inclusion projection k Phi hSplit hXi hRegular.
have [P [hDistinguished hImage]]:=@analytic_prepared_polynomial_image R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXiActual B embed variable coefficient hP J hJ
  k W Wi (weierstrass_preparation_polynomial hPreparation).
have [F [hPrimes hFactor]]:=@analytic_distinguished_polynomial_factorization R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiActual B embed variable coefficient hP J hJ
  hUFD P k hDistinguished.
have [q [hRepQ hValueQ]]:=weierstrass_preparation_unit_value hPreparation.
have hUnitQ:is_commutative_unit Q.
  rewrite -hRepQ;exact:(@analytic_germ_unit_iff_nonzero_value R X NX hNX 0 q).2 hValueQ.
have [u hInverse]:=hUnitQ.
exists u,F;split;first exact:commutative_inverse_unit hInverse.
split;first exact:hPrimes.
rewrite -hFactor hImage -(weierstrass_preparation_identity hPreparation) mulrA hInverse mul1r.
reflexivity.
Qed.
