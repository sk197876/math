(** Federer (1969), 3.4.7, p. 325: a
    nontrivial analytic factorization of the original prepared
    polynomial gives a nontrivial factorization in its transverse
    polynomial subring. Original division proves prime comparison;
    specialization and degree descent give the reflected factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermValueSealed AnalyticGermDomain
  WeierstrassTransverseUP WeierstrassTransversePullback CommutativeDomainUP
  CommutativeFactorizationUP CommutativePrimeLaws CommutativePolynomialUP
  CommutativePolynomialSealed CommutativePolynomialEvaluationUP CommutativePolynomialDegree
  CommutativePolynomialProductDegree PolynomialMonicPrimeBounds
  PolynomialCoefficientMapSealed GaussPolynomialFactorization DistinguishedPolynomialUP
  DistinguishedPolynomialPrimeStep AnalyticDistinguishedPolynomialPrime.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FactorReflection.
Variable R:realType.
Variables X K:lmodType R.
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_real_norm NX) (hNK:is_real_norm NK).
Variable v:X.
Variable xi:Hom X R^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@analytic_representative_type R X NX hNX 0.
Hypothesis hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi.
Hypothesis hXiValues:forall x,analytic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R K NK hNK (projection 0))].
Local Notation E:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).
Local Notation value:=(@AnalyticGermValue.map R K NK hNK (projection 0)).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.



(** Source for [analytic_distinguished_factor_reflection]: the
    nontrivial factor reflection in the final paragraph of
    3.4.7, p. 325. Both reflected factors are
    monic distinguished polynomials of positive degree and
    their degrees add to the original degree. The proof
    expands the source through original division and prime
    comparison rather than preparing the two given factors. *)
Theorem analytic_distinguished_factor_reflection
    (hUFD:is_unique_factorization_commutative_domain A) (P:B) k (f g:G):
  is_distinguished_polynomial coefficient value P k ->(0<k)%N ->
  J P = f*g ->~is_commutative_unit f ->~is_commutative_unit g ->
  exists H Q:B,exists m n:nat,
    is_distinguished_polynomial coefficient value H m /\
    is_distinguished_polynomial coefficient value Q n /\
    (0<m)%N /\(0<n)%N /\(m+n=k)%N /\P = H*Q.
Proof.
move=>hDistinguished hPositive hProduct hF hG.
pose D:comNzRingType:=@CommutativePolynomial.space R.
pose embedR:{rmorphism R->D}:=@CommutativePolynomial.embed R.
pose variableR:D:=@CommutativePolynomial.variable R.
pose target:=@CommutativePolynomial.coefficient R.
have hTarget:=@CommutativePolynomial.laws R.
pose M:{rmorphism B->D}:=@PolynomialCoefficientMap.map A B R D embed variable coefficient
  embedR variableR target hP hTarget value.
have hMap:=@PolynomialCoefficientMap.laws A B R D embed variable coefficient
  embedR variableR target hP hTarget value.
have hDomainR:is_commutative_integral_domain R.
  move=>x y /eqP;rewrite mulf_eq0=>/orP[/eqP h|/eqP h];[by left|by right].
have hPolynomialUFD:=@gauss_polynomial_prime_factorization A B embed variable coefficient hP hUFD.
have [H [Q [m [n [hH [hPrimeH [hQ [hSmaller hRestore]]]]]]]]:=
  @distinguished_polynomial_prime_step A B R D embed variable coefficient hP
    embedR variableR target hTarget value M hMap hUFD.1 hDomainR hPolynomialUFD
    P k hDistinguished hPositive.
have hPrime:=@analytic_distinguished_polynomial_prime R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiValues B embed variable coefficient hP J hJ
  hUFD.1 H m hH hPrimeH.
have hPositiveM:=@polynomial_monic_prime_positive_degree A B embed variable coefficient
  hP H m hH.1 hPrimeH.
have hPositiveN:(0<n)%N.
  case:(posnP n)=>[hZero|hPosN];last by [].
  rewrite hZero in hQ.
  exfalso.
  have hOne:=@polynomial_monic_degree_zero_one A B embed variable coefficient hP Q hQ.1.
  rewrite hOne mulr1 in hRestore.
  have hEqual:J H = f*g by rewrite -hRestore.
  have hIrreducible:=@commutative_prime_irreducible G
    (@analytic_germ_no_zero_divisors R X NX hNX 0) (J H) hPrime.
  case:(hIrreducible.2.2 f g hEqual)=>h;[exact:hF h|exact:hG h].
have hDegreeProduct:=@polynomial_product_degree A B embed variable coefficient hP hUFD.1
  H Q m n hH.1.1 hQ.1.1.
rewrite -hRestore in hDegreeProduct.
have hDegreeSum:=@polynomial_degree_unique A B coefficient P (m+n)%N k
  hDegreeProduct hDistinguished.1.1.
exists H,Q,m,n;split;first exact:hH.
split;first exact:hQ.
split;first exact:hPositiveM.
split;first exact:hPositiveN.
by split.
Qed.
End FactorReflection.
