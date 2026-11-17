(** Federer (1969), 3.4.8(10), pp. 330–331:
    the original distinguished kernel polynomial
    has derivative outside I_g. Apply the
    earlier minimal-polynomial separability theorem to
    the actual original coefficient-field data. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermRing AnalyticGermFactorization AnalyticCoordinateGermsSealed AnalyticPrefixGermMap
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionFieldInputs AnalyticReductionFaithfulPrefix
  CommutativeIdealUP CommutativeQuotientUP CommutativeFactorizationUP FractionFieldUP
  CoefficientFractionFieldUP CoefficientFaithfulFractionField IntegralRingElementUP
  CommutativePolynomialUP CommutativePolynomialMonicUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed PolynomialScalarComposition
  PolynomialCoefficientMapUP PolynomialCoefficientMapSealed IntegralMinimalPolynomialDescent FieldPolynomialMinimumUP AnalyticReductionMinimalPolynomial AnalyticReductionDistinguishedPolynomial
  AnalyticScalarsSealed AnalyticGermValueSealed DistinguishedPolynomialUP FormalPolynomialDerivativeUP
  MinimalDerivativeCoefficientDescent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SeparableOriginal.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Hypothesis hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hProper:~I 1.
Variable g:@orthogonal_group R X B hB n e he.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient (@analytic_rotated_germ_ideal R X B hB n e he I g) pi.
Variable m:'I_n.
Hypothesis hMN:((m:nat)<=n)%N.
Hypothesis hAllB:forall j:'I_n,(m<=j)%N ->@analytic_reduction_actual_B R X B hB n e he omega I j g.
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)].
Local Notation A1:=[the comNzRingType of (@analytic_germ_ring R (R_n R (m:nat).+1)
  (inner_norm (@euclidean_inner_productP R (m:nat).+1))
  (inner_norm_real_norm (@euclidean_inner_productP R (m:nat).+1)) 0)].
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Local Notation E1:=(@analytic_prefix_germ_map R X NX hNX n e he omega (m:nat).+1 (ltn_ord m)).
Local Notation scalar:=(GRing.RMorphism.clone A C (pi \o E) _).
Local Notation gamma:=(fun j:'I_n=>@AnalyticCoordinateGerms.value R X NX hNX n e he omega j).
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


(** Source for [analytic_reduction_separable_original_polynomial]:
    the original W'_(m+1) is nonzero
    modulo I_g and belongs to the
    original bounded coefficient module,
    3.4.8(10), pp. 330–331. This theorem
    proves the nonzero quotient assertion from
    the existing separability theorem. Actual analytic
    directional differentiation is connected separately. *)
Theorem analytic_reduction_separable_original_polynomial:
  (0<m)%N ->~@analytic_reduction_actual_A R X B hB n e he omega I (widen_ord (leqnSn n) m) g ->
  exists (W:P) k,(0<k)%N /\
    is_distinguished_polynomial coefficient
      (@AnalyticGermValue.map R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
        (inner_norm_real_norm (@euclidean_inner_productP R m)) 0) W k /\
    (forall T:P,@analytic_rotated_germ_ideal R X B hB n e he I g (J T) <->
      commutative_divides W T) /\
    (forall derivative:P,is_formal_polynomial_derivative coefficient W derivative ->
      ~@analytic_rotated_germ_ideal R X B hB n e he I g (J derivative)).
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
have [W [H [k [hH [hMapW [hMonic hKernel]]]]]]:=@analytic_reduction_original_minimal_data
  R X B hB n e he hON omega hDual I hI hProper g C pi hPi m hMN hAllB
  L M inclusion hFraction eta phi hCoefficient P embed variable coefficient hP J hJ
  PM embedM variableM target hM map hMap F hF hPositive hNotA.
have hDistinguished:=@analytic_reduction_monic_kernel_distinguished R X B hB n e he omega hDual
  I hI hProper g m hMN hAllB P embed variable coefficient hP J hJ W k hMonic hKernel.
pose realScalar:{rmorphism R->M}:=GRing.RMorphism.clone R M (eta \o
  (@AnalyticScalars.map R (R_n R m) (inner_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)) _.
have hCharacteristic:[pchar M] =i pred0.
  move=>p;rewrite (fmorph_pchar realScalar);exact:(@pchar_num R p).
pose chi:{rmorphism A->L}:=GRing.RMorphism.clone A L (inclusion \o scalar) _.
pose EJ:{rmorphism P->C}:=GRing.RMorphism.clone P C (pi \o J) _.
pose EL:{rmorphism P->L}:=GRing.RMorphism.clone P L (inclusion \o EJ) _.
have hEJ:=@polynomial_evaluation_after_ring_map A P G C embed variable E (gamma m) J pi hJ.
have hEL:=@polynomial_evaluation_after_ring_map A P C L embed variable scalar (pi (gamma m)) EJ inclusion hEJ.
have hTriangle a:chi a = phi (eta a):=esym (coefficient_fraction_scalar_triangle hCoefficient a).
have hMinimum:is_minimal_field_polynomial target F (map W) k by rewrite hMapW.
exists W,k;split;first exact:minimal_field_polynomial_positive hH.
split;first exact:hDistinguished.
split;first exact:hKernel.
move=>derivative hDerivative hIn.
have hNonzero:=@original_minimal_derivative_nonzero A P M PM L embed variable coefficient
  embedM variableM target hP hM eta map hMap chi phi (inclusion (pi (gamma m))) EL F W k
  hTriangle hEL hF hMinimum hCharacteristic derivative hDerivative.
apply:hNonzero;change (inclusion (pi (J derivative)) = 0).
by rewrite (commutative_quotient_kernel hPi _).2 // rmorph0.
Qed.
End SeparableOriginal.
