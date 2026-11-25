(** Federer (1969), 3.4.8(10), p. 330:
    the original prepared polynomial is expressed
    in the coefficient germs at zero.
    Reuse original preparation and polynomial
    coefficient independence through the proved
    equal-centre germ identifications. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP AnalyticGermRepresentatives
  AnalyticGermUP AnalyticGermRing AnalyticGermValueSealed WeierstrassTransverseUP
  WeierstrassTransversePullback WeierstrassRegularUP WeierstrassPreparationUP WeierstrassPreparationExistence
  AnalyticPreparedPolynomialImage AnalyticTransversePolynomialInjection
  PointedAnalyticPullbackUP PointedAnalyticPullbackComposition PointedAnalyticPullbackValue
  OrdinaryPointedAnalyticPullback EqualAnalyticGermCentres
  CommutativeIdealUP CommutativePolynomialUP CommutativePolynomialSealed CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed PolynomialCoefficientMapSealed PolynomialMonicCoefficientMap
  PolynomialEvaluationCoefficientExtension PolynomialCoefficientSurjection DistinguishedPolynomialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalPolynomial.
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

(** Source for [analytic_original_prepared_polynomial]:
    the original prepared polynomial in the
    faithful prefix polynomial ring, 3.4.8(10),
    p. 330. Its lower coefficient values
    vanish at zero. The same original
    polynomial evaluation is injective by the
    earlier coefficient-independence theorem, not by
    a new transcendence argument. *)
Theorem analytic_original_prepared_polynomial (I:set G) (Phi:G) k:
  is_commutative_ideal I ->I Phi ->is_weierstrass_regular_germ Phi k v ->
  injective J /\exists H:P,
    is_distinguished_polynomial coefficient (@AnalyticGermValue.map R K NK hNK 0) H k /\I (J H).
Proof.
move=>hI hPhi hRegular.
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
pose map:=@PolynomialCoefficientMap.map A B A0 P embedA variableA source embed variable coefficient hA hP T.
have hMap:=@PolynomialCoefficientMap.laws A B A0 P embedA variableA source embed variable coefficient hA hP T.
have hTriangle a:old a = E0 (T a) by rewrite hScalar hTF.
have hDiagram:=@polynomial_evaluation_coefficient_extension A B A0 P G embedA variableA source
  embed variable coefficient hA hP T map hMap old E0 Gamma JA J hTriangle hJA hJ.
have hOnto:forall a:A0,exists b:A,T b = a by move=>a;exists (F a);exact:hFT a.
have hSurjective:=@polynomial_coefficient_map_surjective A B A0 P embedA variableA source
  embed variable coefficient hA hP T map hOnto hMap.
have hInjectiveA:=@analytic_transverse_polynomial_evaluation_injective R X K NX NK hNX hNK
  v xi inclusion projection hSplit fXi B embedA variableA source hA JA hJA hXiValues.
split.
- move=>a b hEqual.
  have [a0 hA0]:=hSurjective a;have [b0 hB0]:=hSurjective b.
  have hOldEqual:JA a0 = JA b0 by rewrite !hDiagram hA0 hB0.
  have hAB:=@hInjectiveA a0 b0 hOldEqual;by rewrite -hA0 -hB0 hAB.
- have [Q [W [Wi hPreparation]]]:=@weierstrass_preparation_with_transverse_exists R X K NX NK hNX hNK
    v xi inclusion projection k Phi hSplit hXi hRegular.
  have [H [hDistinguished hH]]:=@analytic_prepared_polynomial_image R X K NX NK hNX hNK
    v xi inclusion projection hSplit fXi hXiValues B embedA variableA source hA JA hJA k W Wi
    (weierstrass_preparation_polynomial hPreparation).
  have hIn:I (JA H).
    rewrite hH -(weierstrass_preparation_identity hPreparation).
    exact:(@commutative_ideal_mul G I hI Q Phi hPhi).
  exists (map H);split.
  + split.
    * exact:(@polynomial_coefficient_map_monic_degree A A0 B P source coefficient T map H k hMap hDistinguished.1).
    * move=>i hSmall;rewrite hMap.
      have hValue:=@pointed_analytic_pullback_centre_value R K K NK NK hNK hNK 0 (projection 0)
        idfun T hT (esym (linear0 projection)) (source H i).
      rewrite hValue;exact:hDistinguished.2 i hSmall.
  + rewrite -hDiagram;exact:hIn.
Qed.
End OriginalPolynomial.
