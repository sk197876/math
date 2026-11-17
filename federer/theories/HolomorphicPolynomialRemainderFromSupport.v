(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: the original
    polynomial subring has the actual directional degree
    used by analytic division. Finite coefficient support
    implies the all-point derivative condition on an actual
    neighbourhood, rather than just vanishing jets at zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm HolomorphicLinear HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormAnalyticUP
  HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermRing
  HolomorphicTransversePolynomialRepresentative ComplexWeierstrassTransverseUP ComplexWeierstrassTransversePullback
  ComplexWeierstrassDivisionUP ComplexWeierstrassFiniteRemainderVanishing CommutativePolynomialUP
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PolynomialRemainder.
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

(** Source for [holomorphic_polynomial_support_directional_remainder]:
    each original polynomial with support strictly below k
    gives a genuine analytic directional remainder, supporting
    the uniqueness argument in 3.4.7, p. 325. *)
Theorem holomorphic_polynomial_support_directional_remainder (P:B) k:
  (forall x,holomorphic_representative_value fXi x = xi x) ->
  (forall i,(k<=i)%N ->coefficient P i = 0) ->
  @is_complex_directional_polynomial_germ R X NX (complex_norm_real hNX) k v (J P).
Proof.
move=>hXiValues hSupport.
have hRepresentatives i:=@holomorphic_germ_has_representative R K NK (complex_norm_real hNK) (projection 0) (coefficient P i).
pose c i:=projT1 (cid (hRepresentatives i)).
have hC i:holomorphic_germ (c i) = coefficient P i:=projT2 (cid (hRepresentatives i)).
have [f [hValues hGerm]]:=@holomorphic_transverse_polynomial_representative R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi k c hXiValues.
have hRep:(holomorphic_germ f:G) = J P.
  rewrite hGerm (@polynomial_evaluation_finite_expression A B G embed variable coefficient
    hP E Gamma J hJ P k hSupport).
  apply:eq_bigr=>i _;by rewrite hC.
pose C i x:=holomorphic_representative_value (c i) (projection x).
have hExpression:holomorphic_representative_value f =
    (fun x=>\sum_(i<k) (xi x)^+i*C i (inclusion (projection x))).
  apply:funext=>x;rewrite hValues;apply:eq_bigr=>i _.
  by rewrite /C (complex_weierstrass_transverse_left_inverse hSplit).
have [U [haU hf]]:=holomorphic_representative_holomorphic f.
exists f;split;first exact:hRep.
exists U;split;first exact:haU.
split;first exact:hf.
rewrite hExpression.
apply:(@complex_weierstrass_finite_remainder_vanishing R X K NX NK (complex_norm_real hNX) v xi inclusion projection k C U hSplit).
by rewrite -hExpression;exact:hf.1.
Qed.
End PolynomialRemainder.
