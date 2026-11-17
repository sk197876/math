(** Federer (1969), 3.4.8(10), p. 331:
    division by the original distinguished
    prefix polynomial has a bounded remainder
    in the original coefficient germs at
    zero. Transfer the existing analytic
    division through the proved equal-centre maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermValueSealed WeierstrassTransverseUP
  WeierstrassTransversePullback WeierstrassRegularUP
  PointedAnalyticPullbackUP PointedAnalyticPullbackComposition PointedAnalyticPullbackValue
  OrdinaryPointedAnalyticPullback EqualAnalyticGermCentres
  CommutativePolynomialUP CommutativePolynomialSealed CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed PolynomialCoefficientMapSealed PolynomialMonicCoefficientMap
  PolynomialEvaluationCoefficientExtension DistinguishedPolynomialUP AnalyticPolynomialDivisionModel AnalyticDistinguishedPolynomialLine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalDivision.
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
Local Notation A0:=[the comNzRingType of (@analytic_germ_ring R K NK hNK 0)].
Local Notation old:=(@weierstrass_transverse_ring_pullback R X K NX NK hNX hNK
  v xi inclusion projection hSplit).
Local Notation Gamma:=(analytic_germ fXi:G).
Variable E0:{rmorphism A0->G}.
Hypothesis hE0:is_pointed_analytic_germ_pullback projection E0.
Variable P:comNzRingType.
Variable embed:{rmorphism A0->P}.
Variable variable:P.
Variable coefficient:P->nat->A0.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E0 Gamma J.


(** Source for [analytic_original_distinguished_division]:
    the original finite polynomial remainder
    used in the coordinate induction,
    3.4.8(10), p. 331. Original
    preparation gives the positive distinguished
    divisor. The registered analytic division
    theorem supplies quotient and remainder;
    coefficient maps identify their original centres. *)
Theorem analytic_original_distinguished_division (H:P) k:
  is_distinguished_polynomial coefficient (@AnalyticGermValue.map R K NK hNK 0) H k ->
  (0<k)%N ->forall x:G,exists a:G,exists r:P,
    (forall i,(k<=i)%N ->coefficient r i = 0) /\x = a*J H+J r.
Proof.
move=>hDistinguished hPositive x.
have [F [T [hF [hT [hFT hTF]]]]]:=@equal_analytic_germ_centres_ring_witnesses R K NK hNK
  0 (projection 0) (esym (linear0 projection)).
have hOld:=@ordinary_analytic_ring_pullback_pointed_laws R X K NX NK hNX hNK setT projection 0
  (@weierstrass_transverse_projection_analytic R X K NX NK hNX hNK v xi inclusion projection hSplit).
have hComposite:=pointed_analytic_pullback_composes hOld hF.
have hScalar a:E0 a = old (F a).
  exact:(@pointed_analytic_pullback_map_extensional R X K NX NK hNX hNK 0 0 projection
    (fun x=>idfun (projection x)) E0 (fun a=>old (F a)) hE0 hComposite (fun _=>erefl) a).
pose B:=CommutativePolynomial.space A.
pose embedA:=CommutativePolynomial.embed A.
pose variableA:=CommutativePolynomial.variable A.
pose source:=@CommutativePolynomial.coefficient A.
have hA:=CommutativePolynomial.laws A.
pose JA:=@CommutativePolynomialEvaluation.map A B G embedA variableA source hA old Gamma.
have hJA:=@CommutativePolynomialEvaluation.laws A B G embedA variableA source hA old Gamma.
pose forward:=@PolynomialCoefficientMap.map A0 P A B embed variable coefficient embedA variableA source hP hA F.
have hForward:=@PolynomialCoefficientMap.laws A0 P A B embed variable coefficient embedA variableA source hP hA F.
pose back:=@PolynomialCoefficientMap.map A B A0 P embedA variableA source embed variable coefficient hA hP T.
have hBack:=@PolynomialCoefficientMap.laws A B A0 P embedA variableA source embed variable coefficient hA hP T.
have hForwardTriangle a:E0 a = old (F a):=hScalar a.
have hForwardDiagram:=@polynomial_evaluation_coefficient_extension A0 P A B G embed variable coefficient
  embedA variableA source hP hA F forward hForward E0 old Gamma J JA hForwardTriangle hJ hJA.
have hBackTriangle a:old a = E0 (T a) by rewrite hScalar hTF.
have hBackDiagram:=@polynomial_evaluation_coefficient_extension A B A0 P G embedA variableA source
  embed variable coefficient hA hP T back hBack old E0 Gamma JA J hBackTriangle hJA hJ.
have hOldDistinguished:is_distinguished_polynomial source (@AnalyticGermValue.map R K NK hNK (projection 0)) (forward H) k.
  split.
  - exact:(@polynomial_coefficient_map_monic_degree A0 A P B coefficient source F forward H k hForward hDistinguished.1).
  - move=>i hSmall;rewrite hForward.
    have hValue:=@pointed_analytic_pullback_centre_value R K K NK NK hNK hNK (projection 0) 0
      idfun F hF (linear0 projection) (coefficient H i).
    rewrite hValue;exact:hDistinguished.2 i hSmall.
have hRegular:=@analytic_distinguished_polynomial_regular R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXiValues B embedA variableA source hA JA hJA
  (forward H) k hOldDistinguished hPositive.
have [a [r [hBound hEquation]]]:=@analytic_polynomial_division_exists R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi hXi hXiValues B embedA variableA source hA JA hJA
  (forward H) k hRegular x.
exists a,(back r);split.
- move=>i hI;by rewrite hBack hBound // rmorph0.
- rewrite -(hBackDiagram r) (hForwardDiagram H);exact:hEquation.
Qed.
End OriginalDivision.
