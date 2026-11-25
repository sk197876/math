(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the
    original distinguished polynomial restricts on the chosen
    line to t^k. Its actual analytic representative
    supplies regularity and noninvertibility, with no assumed
    directional-derivative or factorization conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws HolomorphicGermRing HolomorphicGermValueUP HolomorphicGermValueSealed
  HolomorphicGermValueUnits HolomorphicTransversePolynomialRepresentative
  ComplexWeierstrassTransverseUP ComplexWeierstrassTransverseLaws ComplexWeierstrassTransversePullback
  ComplexWeierstrassRegularUP ComplexWeierstrassLineRegularity CommutativeFactorizationUP
  CommutativePolynomialUP CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws
  DistinguishedPolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ActualLine.
Variable R:realType.
Variables X K:lmodType (ComplexScalars.C R).
Variables (NX:X->R) (NK:K->R).
Variables (hNX:is_complex_norm NX) (hNK:is_complex_norm NK).
Variable v:X.
Variable xi:Hom X (ComplexScalars.C R)^o.
Variables (inclusion:Hom K X) (projection:Hom X K).
Hypothesis hSplit:is_complex_weierstrass_transverse_space NX NK v xi inclusion projection.
Variable fXi:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0.
Hypothesis hXiValues:forall x,holomorphic_representative_value fXi x = xi x.
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0)].
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R K NK (complex_norm_real hNK) (projection 0))].
Local Notation E:=(@complex_weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(holomorphic_germ fXi:G).
Local Notation value:=(@HolomorphicGermValue.map R K NK (complex_norm_real hNK) (projection 0)).
Variable B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism B->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E Gamma J.

(** Source for [holomorphic_distinguished_polynomial_line_representative]:
    the original equation W(tv)=t^k has an actual
    analytic representative, supporting the factor argument
    in 3.4.7, p. 325. Degree zero is retained. *)
Theorem holomorphic_distinguished_polynomial_line_representative (P:B) k:
  is_distinguished_polynomial coefficient value P k ->
  exists f:@holomorphic_representative_type R X NX (complex_norm_real hNX) 0,
    (holomorphic_germ f:G) = J P /\
    forall t:ComplexScalars.C R,holomorphic_representative_value f (t*:v) = t^+k.
Proof.
move=>hDistinguished.
have hSupport i (hi:(k.+1<=i)%N):coefficient P i = 0:=hDistinguished.1.1.2 i hi.
have hRepresentatives i:=@holomorphic_germ_has_representative R K NK (complex_norm_real hNK) (projection 0) (coefficient P i).
pose c i:=projT1 (cid (hRepresentatives i)).
have hC i:holomorphic_germ (c i) = coefficient P i:=projT2 (cid (hRepresentatives i)).
have [f [hValues hGerm]]:=@holomorphic_transverse_polynomial_representative R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi k.+1 c hXiValues.
exists f;split.
- rewrite hGerm (@polynomial_evaluation_finite_expression A B G embed variable coefficient
    hP E Gamma J hJ P k.+1 hSupport).
  apply:eq_bigr=>i _;by rewrite hC.
- move=>t.
  have hCoordinate:xi (t*:v) = t.
    have h:=@complex_weierstrass_line_functional_coordinate R X K NX NK v xi inclusion projection hSplit t 0.
    by rewrite linear0 addr0 in h.
  have hProjection:projection (t*:v) = projection 0.
    have h:=@complex_weierstrass_line_transverse_coordinate R X K NX NK v xi inclusion projection hSplit t 0.
    rewrite linear0 addr0 in h.
    by rewrite linear0.
  have hValue i:holomorphic_representative_value (c i) (projection 0) = value (coefficient P i).
    by rewrite -(hC i) (@HolomorphicGermValue.laws R K NK (complex_norm_real hNK) (projection 0)).
  rewrite hValues.
  under eq_bigr do rewrite hCoordinate hProjection hValue.
  rewrite (bigD1 (Ordinal (ltnSn k))) //= hDistinguished.1.2 rmorph1 mulr1.
  have hRest:(\sum_(i<k.+1 | i!=Ordinal (ltnSn k)) t^+i*value (coefficient P i)) = 0.
    apply:big1=>i hi.
    have hNe:((i:nat)!=k)%N by move:hi;rewrite -val_eqE /=.
    have hLe:(i<=k)%N by move:(ltn_ord i);rewrite ltnS.
    have hSmall:(i<k)%N by rewrite ltn_neqAle hNe hLe.
    by rewrite hDistinguished.2 // mulr0.
  by rewrite hRest addr0.
Qed.

(** Source for [holomorphic_distinguished_polynomial_regular]: a
    positive-degree original distinguished polynomial satisfies
    exactly the regularity premise of 3.4.6, as used
    for its factors in 3.4.7, p. 325. *)
Theorem holomorphic_distinguished_polynomial_regular (P:B) k:
  is_distinguished_polynomial coefficient value P k ->(0<k)%N ->
  @is_complex_weierstrass_regular_germ R X NX hNX (J P) k v.
Proof.
move=>hDistinguished hPositive.
have [f [hGerm hLine]]:=holomorphic_distinguished_polynomial_line_representative hDistinguished.
have hExact t:holomorphic_representative_value f (t*:v) = 1*t^+k by rewrite mul1r;exact:hLine.
have h:=@complex_weierstrass_line_regularity R X NX hNX f k v 1 hPositive (oner_neq0 (ComplexScalars.C R)) hExact.
by rewrite hGerm in h.
Qed.

(** Source for [holomorphic_distinguished_polynomial_nonunit]: a
    positive-degree original distinguished factor has value
    zero at the centre and is not a unit, supporting
    3.4.7, p. 325. *)
Theorem holomorphic_distinguished_polynomial_nonunit (P:B) k:
  is_distinguished_polynomial coefficient value P k ->(0<k)%N ->
  ~is_commutative_unit (J P).
Proof.
move=>hDistinguished hPositive hUnit.
have [f [hGerm hLine]]:=holomorphic_distinguished_polynomial_line_representative hDistinguished.
have hNonzero:=(@holomorphic_germ_value_unit_equivalence R X NX (complex_norm_real hNX) 0 (J P)).1 hUnit.
apply:hNonzero;rewrite -hGerm (@HolomorphicGermValue.laws R X NX (complex_norm_real hNX) 0).
have hZero:=hLine 0.
have hK:k!=0%N by rewrite -lt0n.
by rewrite scale0r expr0n (negbTE hK) in hZero.
Qed.
End ActualLine.
