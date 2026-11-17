(** Federer (1969), 3.4.8(8), pp. 326,
    329–330: for the original prime ideal
    and original g in every required B_j,
    almost every original suffix rotation
    gives C_m and all required B_j.
    Quotients, fraction fields and coefficient
    fields are local witnesses obtained from
    the existing sealed interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed IsotropyGroupTopology
  HaarIntegralUP MeasureUP MeasureAlmostBasic AnalyticGermRing AnalyticScalarsSealed AnalyticCoordinateGermsSealed
  AnalyticPrefixGermMap AnalyticOrthogonalPullback AnalyticRotatedGermIdeal AnalyticRotatedIdealPrime AnalyticReductionActual
  AnalyticReductionFieldInputs AnalyticReductionPrimitiveHaar AnalyticPrimitiveRotationRelations
  AnalyticIntegralRotationDirections CommutativeIdealUP CommutativeSubringUP CommutativeQuotientSealed CommutativeQuotientLaws
  FractionFieldSealed CoefficientFractionFieldSealed OrthogonalCoordinateFixing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalSuffixTheorem.
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
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variable I:set G.
Variable g:O.
Variable m:'I_n.
Local Notation H:=(@analytic_suffix_rotation_group R X B hB n e he m).
Local Notation Cm:=(@analytic_reduction_actual_C R X B hB n e he omega I m).
Local Notation Bj:=(@analytic_reduction_actual_B R X B hB n e he omega I).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Hypothesis hH:is_subgroup_restriction mulO invO unitO H mulH invH unitH.

(** Source for [analytic_reduction_suffix_haar_almost_C_B]:
    the complete original assertion 3.4.8(8),
    p. 326, proved on pp. 329–330.
    Exactly the printed prime-ideal and B_j
    hypotheses remain. Actual finite quotient
    generation, integral relations, primitive real
    directions, original denominators and suffix
    Haar transport are proved internally.
    The coefficient map may have a kernel. *)
Theorem analytic_reduction_suffix_haar_almost_C_B (mu:set H->\bar R):
  is_prime_commutative_ideal I ->
  (forall j:'I_n,(m<=j)%N ->Bj j g) ->is_left_haar_measure mulH mu ->
  mu [set q:H|~(Cm (mulO g (set_val q)) /\forall j:'I_n,(m<=j)%N ->Bj j (mulO g (set_val q)))] = 0%:E.
Proof.
move=>hPrime hAllB hMu.
pose hMN:=leq_trans (leqnSn (m:nat)) (ltn_ord m).
pose Ig:=@analytic_rotated_germ_ideal R X B hB n e he I g.
have hPrimeRot:=@analytic_rotated_germ_ideal_prime R X B hB n e he I g hPrime.
pose realG:=@AnalyticScalars.map R X NX hNX 0.
pose C:=@CommutativeIdealQuotient.space R G realG Ig hPrimeRot.1 hPrimeRot.2.1.
pose pi:=@CommutativeIdealQuotient.projection R G realG Ig hPrimeRot.1 hPrimeRot.2.1.
have hPi:=@CommutativeIdealQuotient.laws R G realG Ig hPrimeRot.1 hPrimeRot.2.1.
have hDomain:=@prime_commutative_quotient_domain G C Ig pi hPi hPrimeRot.
pose L:=@FractionField.space C hDomain.
pose inclusion:=@FractionField.embed C hDomain.
have hFraction:=@FractionField.laws C hDomain.
pose A:=[the comNzRingType of (@analytic_germ_ring R (R_n R m)
  (inner_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R m)) 0)].
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega m hMN.
pose scalar:{rmorphism A->C}:=GRing.RMorphism.clone A C (pi \o E) _.
pose original:{rmorphism A->L}:=GRing.RMorphism.clone A L (inclusion \o scalar) _.
pose M:=@CoefficientFractionField.space A L original.
pose eta:=@CoefficientFractionField.scalar A L original.
pose phi:=@CoefficientFractionField.inclusion A L original.
have hCoefficient:=@CoefficientFractionField.laws A L original.
have hPrimitiveNull:=@analytic_reduction_original_primitive_haar_null R X B hB n e he hON omega hDual
  I hPrime.1 hPrime.2.1 g C pi hPi m hMN hAllB L M inclusion hFraction eta phi hCoefficient
  mulO invO unitO hO mulH invH unitH hH mu hMu.
have hIntegral:=@analytic_reduction_quotient_integral R X B hB n e he hON omega hDual
  I hPrime.1 hPrime.2.1 g C pi hPi m hMN hAllB.
pose bad:=fun q:H=>~(Cm (mulO g (set_val q)) /\forall j:'I_n,(m<=j)%N ->Bj j (mulO g (set_val q))).
pose primitiveBad:=fun q:H=>~is_generated_commutative_subring
  (fun y:L=>y = inclusion (pi (@analytic_orthogonal_germ_map R X B hB n e he
    (invO (set_val q)) (@AnalyticCoordinateGerms.value R X NX hNX n e he omega m))) \/
    exists a:M,y = phi a) setT.
have hSubset:bad `<=` primitiveBad.
  move=>q hBad hGenerated;apply:hBad;split.
  - exact:(@analytic_reduction_primitive_rotation_C R X B hB n e he hON omega hDual I g C pi hPi
      m hMN L M inclusion hFraction eta phi hCoefficient mulO invO unitO hO mulH invH unitH hH q hGenerated).
  - move=>j hMJ.
    exact:(@analytic_integral_suffix_rotation_B R X B hB n e he hON omega hDual I g C pi hPi
      m hMN hIntegral mulO invO unitO hO mulH invH unitH hH q j hMJ).
have [lambda [hLambda hMeasure hRep hRegular]]:=hMu.
exact:(@measure_null_subset R (Choice.clone H _) mu hMeasure bad primitiveBad hSubset hPrimitiveNull).
Qed.
End OriginalSuffixTheorem.
