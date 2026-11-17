(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 330:
    the original faithful holomorphic coefficient ring
    contains the coefficients of the next
    coordinate's monic minimal polynomial. Reuse
    the established original quotient integrality,
    faithful fractions and monic kernel descent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexOrderedBases HermitianUP HermitianRealImaginary HermitianComplexNorm UnitaryGroup HolomorphicCoordinateNorm FieldCoordinateFunctional Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  HolomorphicGermRing HolomorphicGermFactorization HolomorphicCoordinateGermsSealed HolomorphicPrefixGermMap
  HolomorphicRotatedGermIdeal HolomorphicReductionActual HolomorphicReductionOriginalFieldInputs HolomorphicReductionFaithfulPrefix
  CommutativeIdealUP CommutativeQuotientUP CommutativeFactorizationUP FractionFieldUP
  CoefficientFractionFieldUP CoefficientFaithfulFractionField IntegralRingElementUP
  CommutativePolynomialUP CommutativePolynomialMonicUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed PolynomialScalarComposition
  PolynomialCoefficientMapUP PolynomialCoefficientMapSealed IntegralMinimalPolynomialDescent FieldPolynomialMinimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalMinimal.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable Herm:X->X->ComplexScalars.C R.
Hypothesis hHerm:is_hermitian_product Herm.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part Herm).
Local Notation hB:=(hermitian_real_inner_product hHerm).
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family Herm e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hHerm).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable g:@unitary_group R X Herm hHerm (n+n) eR heR.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient (@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g) pi.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Hypothesis hAllB:forall j:'I_n,(m<=j)%N ->@holomorphic_reduction_actual_B R X Herm hHerm n e he omega I j g.
Local Notation A:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R m)) 0)].
Local Notation A1:=[the comNzRingType of (@holomorphic_germ_ring R (coordinate_space (ComplexScalars.C R) (m:nat).+1)
  (@holomorphic_coordinate_norm R (m:nat).+1)
  (complex_norm_real (@holomorphic_coordinate_norm_laws R (m:nat).+1)) 0)].
Local Notation E:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega m hMN).
Local Notation E1:=(@holomorphic_prefix_germ_map R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m)).
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o E) _).
Local Notation gamma:=(fun j:'I_n=>@HolomorphicCoordinateGerms.value R X NX hNX n e he omega j).
Variables L M:fieldType.
Variable inclusion:{rmorphism C->L}.
Hypothesis hFraction:is_commutative_fraction_field inclusion.
Variable eta:{rmorphism A->M}.
Variable phi:{rmorphism M->L}.
Hypothesis hCoefficient:is_coefficient_fraction_field
  (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi.


Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E (gamma m) J.

(** Source for [holomorphic_reduction_original_minimal_data]:
    the original monic kernel generator maps
    to the coefficient-field minimal polynomial,
    3.4.8(10), p. 330. Both independent
    polynomial interfaces retain the same original
    coordinate and coefficient maps. *)
Theorem holomorphic_reduction_original_minimal_data
  (PM:comNzRingType) (embedM:{rmorphism M->PM}) (variableM:PM) (target:PM->nat->M)
  (hM:is_commutative_polynomial_ring embedM variableM target)
  (map:{rmorphism P->PM}) (hMap:is_polynomial_coefficient_map coefficient target eta map)
  (F:{rmorphism PM->L})
  (hF:is_commutative_polynomial_evaluation embedM variableM phi (inclusion (pi (gamma m))) F):
  (0<m)%N ->~@holomorphic_reduction_actual_A R X Herm hHerm n e he omega I (widen_ord (leqnSn n) m) g ->
  exists (W:P) (H:PM) k,is_minimal_field_polynomial target F H k /\map W = H /\
    is_monic_polynomial coefficient W k /\
    (forall T:P,@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g (J T) <->
      commutative_divides W T).
Proof.
move=>hPositive hNotA.
pose chi:{rmorphism A->L}:=GRing.RMorphism.clone A L (inclusion \o scalar) _.
have hFaithful:=@holomorphic_reduction_not_A_faithful_prefix R X Herm hHerm n e he omega hDual
  I g C pi m hMN hPi hPositive hNotA.
have hOriginal:injective chi.
  move=>a b hEqual;apply:hFaithful.
  apply:(fraction_field_embedding_injective hFraction);exact:hEqual.
have hField:=@faithful_coefficient_fraction_field A L M chi eta phi hCoefficient hOriginal.
have hUFD:=@finite_holomorphic_germ_ring_factorization R (coordinate_space (ComplexScalars.C R) m)
  (@holomorphic_coordinate_norm R m)
  (@holomorphic_coordinate_norm_laws R m) m (@coordinate_basis (ComplexScalars.C R) m) 0 (@coordinate_basisP (ComplexScalars.C R) m).
have hIntegralC:=@holomorphic_reduction_original_quotient_integral R X Herm hHerm n e he omega hDual
  I hI hProper g C pi hPi m hMN hAllB (pi (gamma m)).
have hIntegral:is_integral_ring_element chi (inclusion (pi (gamma m))).
  have [r [c [hR hEquation]]]:=hIntegralC.
  exists r,c;split;first exact:hR.
  rewrite -(rmorphXn inclusion) hEquation rmorph_sum.
  apply:eq_bigr=>i _;by rewrite rmorphM rmorphXn.
pose EJ:{rmorphism P->C}:=GRing.RMorphism.clone P C (pi \o J) _.
pose EL:{rmorphism P->L}:=GRing.RMorphism.clone P L (inclusion \o EJ) _.
have hEJ:=@polynomial_evaluation_after_ring_map A P G C embed variable E (gamma m) J pi hJ.
have hEL:=@polynomial_evaluation_after_ring_map A P C L embed variable scalar (pi (gamma m)) EJ inclusion hEJ.
have hTriangle a:chi a = phi (eta a):=esym (coefficient_fraction_scalar_triangle hCoefficient a).
have [W [H [k [hH [hMapW [hMonic hKernel]]]]]]:=@integral_minimal_polynomial_original_kernel
  A P M PM L embed variable coefficient embedM variableM target hP hM eta hField hUFD map hMap
  chi phi (inclusion (pi (gamma m))) EL F hTriangle hEL hF hIntegral.
exists W,H,k;split;first exact:hH.
split;first exact:hMapW.
split;first exact:hMonic.
move=>T;rewrite -hKernel.
split.
- move=>hIn;change (inclusion (pi (J T)) = 0).
  by rewrite (commutative_quotient_kernel hPi _).2 // rmorph0.
- move=>hZero;apply:(commutative_quotient_kernel hPi _).1.
  apply:(fraction_field_embedding_injective hFraction).
  change (EL T = inclusion 0);by rewrite hZero rmorph0.
Qed.
(** Source for [holomorphic_reduction_original_minimal_kernel]:
    the monic polynomial in the original
    coefficient germs generates P intersection I_g,
    3.4.8(10), p. 330. Original not-A_m,
    B_j and proper-ideal hypotheses prove every
    algebraic premise. The original finite-dimensional
    holomorphic ring supplies unique factorization. *)
Theorem holomorphic_reduction_original_minimal_kernel:
  (0<m)%N ->~@holomorphic_reduction_actual_A R X Herm hHerm n e he omega I (widen_ord (leqnSn n) m) g ->
  exists (W:P) k,(0<k)%N /\is_monic_polynomial coefficient W k /\
    (forall T:P,@holomorphic_rotated_germ_ideal R X Herm hHerm (n+n) eR heR I g (J T) <->
      commutative_divides W T).
Proof.
move=>hPositive hNotA.
pose PM:=CommutativePolynomial.space M.
pose embedM:=CommutativePolynomial.embed M.
pose variableM:=CommutativePolynomial.variable M.
pose target:=@CommutativePolynomial.coefficient M.
have hM:=CommutativePolynomial.laws M.
pose map:=@PolynomialCoefficientMap.map A P M PM embed variable coefficient embedM variableM target hP hM eta.
have hMap:=@PolynomialCoefficientMap.laws A P M PM embed variable coefficient embedM variableM target hP hM eta.
pose F:=@CommutativePolynomialEvaluation.map M PM L embedM variableM target hM phi (inclusion (pi (gamma m))).
have hF:=@CommutativePolynomialEvaluation.laws M PM L embedM variableM target hM phi (inclusion (pi (gamma m))).
have [W [H [k [hH [_ [hMonic hKernel]]]]]]:=@holomorphic_reduction_original_minimal_data
  PM embedM variableM target hM map hMap F hF hPositive hNotA.
exists W,k;split;first exact:minimal_field_polynomial_positive hH.
by split.
Qed.
End OriginalMinimal.
