(** Federer (1969), 3.4.8(10), p. 331:
    every ideal properly containing the original
    rotated prime ideal meets the original
    coefficient ring outside that ideal. Apply
    the proved original primitive-coordinate and
    inverse-denominator results. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis FiniteCoordinates OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct OrthogonalGroupTopology
  AnalyticGermRing AnalyticGermFactorization AnalyticCoordinateGermsSealed AnalyticPrefixGermMap
  AnalyticRotatedGermIdeal AnalyticReductionActual AnalyticReductionFieldInputs AnalyticReductionFaithfulPrefix AnalyticReductionMinimalPolynomial AnalyticReductionCPrimitive
  CommutativeIdealUP CommutativeQuotientUP CommutativeFactorizationUP FractionFieldUP
  CoefficientFractionFieldUP CoefficientFaithfulFractionField IntegralRingElementUP
  CommutativePolynomialUP CommutativePolynomialMonicUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed PolynomialScalarComposition
  PolynomialCoefficientMapSealed IntegralMinimalPolynomialDescent FieldPolynomialMinimumUP PrimitiveQuotientInverseDenominator
  AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed AnalyticPrefixGermSubring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ProperIdeal.
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


(** Source for [analytic_reduction_proper_ideal_coefficient]:
    every larger ideal meets Q_m outside
    I_g, hence at a nonzero original
    coefficient germ, 3.4.8(10), p. 331.
    The original next coordinate is primitive
    by C_m; its monic kernel and
    bounded inverse representative are already proved. *)
Theorem analytic_reduction_proper_ideal_coefficient:
  (0<m)%N ->~@analytic_reduction_actual_A R X B hB n e he omega I (widen_ord (leqnSn n) m) g ->
  @analytic_reduction_actual_C R X B hB n e he omega I m g ->
  forall K:set G,is_commutative_ideal K ->
    @analytic_rotated_germ_ideal R X B hB n e he I g `<=` K ->
    (exists sigma:G,K sigma /\~@analytic_rotated_germ_ideal R X B hB n e he I g sigma) ->
  exists delta:G,K delta /\
    @AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega m delta /\
    ~@analytic_rotated_germ_ideal R X B hB n e he I g delta /\delta<>0.
Proof.
move=>hPositive hNotA hC K hK hContains [sigma [hSigma hOutside]].
have hPrimitive:=@analytic_reduction_C_next_coordinate_primitive R X B hB n e he hON omega hDual
  I hI hProper g C pi hPi m hMN hAllB L M inclusion hFraction eta phi hCoefficient hC.
have [W [k [hKPositive [hMonic hKernel]]]]:=@analytic_reduction_original_minimal_kernel
  R X B hB n e he hON omega hDual I hI hProper g C pi hPi m hMN hAllB
  L M inclusion hFraction eta phi hCoefficient P embed variable coefficient hP J hJ hPositive hNotA.
have hWIn: (@analytic_rotated_germ_ideal R X B hB n e he I g) (J W).
  apply:(hKernel W).2;exists 1;by rewrite mul1r.
have hDomain:=(@finite_analytic_germ_ring_factorization R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) m (@coordinate_basis R m) 0 (@coordinate_basisP R m)).1.
have hOriginal:is_coefficient_fraction_field (GRing.RMorphism.clone A L (inclusion \o pi \o E) _) eta phi.
  constructor.
  - move=>a;change (phi (eta a) = inclusion (pi (E a))).
    exact:coefficient_fraction_scalar_triangle hCoefficient a.
  - move=>y;have [a [b [hNonzero hValue]]]:=@coefficient_fraction_representation A L M
      (GRing.RMorphism.clone A L (inclusion \o scalar) _) eta phi hCoefficient y.
    exists a,b;split;[exact:hNonzero|exact:hValue].
have [delta [T [hDelta [_ hRelation]]]]:=@primitive_quotient_inverse_original_denominator
  A P G C L M embed variable coefficient hP hDomain E (gamma m) J
  (@analytic_rotated_germ_ideal R X B hB n e he I g) pi inclusion eta phi W k
  hPi hFraction hOriginal hJ hPrimitive hMonic hWIn sigma hOutside.
have hProduct:K (sigma*J T).
  rewrite mulrC;exact:(@commutative_ideal_mul G K hK (J T) sigma hSigma).
have hCoefficientIn:K (E delta).
  have hDifference:=@commutative_ideal_add G K hK (sigma*J T) (-(sigma*J T-E delta))
    hProduct (@commutative_ideal_opp G K hK _ (hContains _ hRelation)).
  by rewrite opprB addrCA subrr addr0 in hDifference.
have hDeltaOutside:~@analytic_rotated_germ_ideal R X B hB n e he I g (E delta).
  move=>hIn.
  have hZero:pi (E delta) = 0:=(commutative_quotient_kernel hPi _).2 hIn.
  have hFieldZero:phi (eta delta) = 0.
    rewrite (coefficient_fraction_scalar_triangle hCoefficient delta).
    change (inclusion (pi (E delta)) = 0);by rewrite hZero rmorph0.
  apply:hDelta;apply:(fmorph_inj phi);by rewrite hFieldZero rmorph0.
exists (E delta);split;first exact:hCoefficientIn.
split.
- have hQ:=@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega.
  rewrite (analytic_coordinate_subring_family_member hQ hMN).
  apply/analytic_prefix_germ_subring_membership;by exists delta.
- split;first exact:hDeltaOutside.
  move=>hZero;apply:hDeltaOutside;rewrite hZero.
  exact:(@commutative_ideal_zero G _ (@analytic_rotated_germ_ideal_is_ideal R X B hB n e he I g hI)).
Qed.
End ProperIdeal.
