(** Federer (1969), 3.4.8(11), p. 334:
    every original B_j witness supplies an
    actual prepared W_j equation in I_g.
    The original positive degree, vanishing lower
    coefficient values and analytic prefix domain
    are proved internally from the earlier preparation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis GrassmannAbbreviations EuclideanInnerProduct NormFiniteLinearBound NormAnalyticUP OrthogonalGroupTopology AnalyticGermUP
  AnalyticGermRing AnalyticGermRepresentatives AnalyticCoordinateGermsSealed AnalyticPrefixCoordinatesSealed
  AnalyticPrefixGermMap AnalyticPrefixGermMapLaws AnalyticRotatedGermIdeal AnalyticReductionActual
  CommutativeIdealUP CommutativePolynomialEvaluationUP CommutativePolynomialSealed CommutativePolynomialEvaluationSealed
  AnalyticPrefixPreparedPolynomial DistinguishedPolynomialActualMonic WeierstrassFunctionalPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section PreparedEquation.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Variable I:set G.
Variable g:@orthogonal_group R X B hB n e he.
Variable j:'I_n.
Local Notation hJN:=(leq_trans (leqnSn (j:nat)) (ltn_ord j)).
Local Notation Y:=(R_n R j).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R j)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R j)).
Local Notation P:=(@AnalyticPrefixCoordinates.projection R X n omega (j:nat) hJN).

(** Source for [analytic_reduction_prepared_equation]:
    the original Weierstrass W_j and M_ij
    chosen in 3.4.8(11), p. 334,
    derived from actual B_j membership. No
    polynomial, equation or coefficient smallness is
    an extra hypothesis of this construction. *)
Theorem analytic_reduction_prepared_equation:
  is_commutative_ideal I ->~I 1 ->
  @analytic_reduction_actual_B R X B hB n e he omega I j g ->
  exists k,exists (U:set Y) (b:'I_k->@analytic_representative_type R Y NY hNY 0)
    (f:@analytic_representative_type R X NX hNX 0),
    (0<k)%N /\ U 0 /\@open (real_norm_metric_space hNY) U /\
    (forall i,@norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R)
      U (analytic_representative_value (b i))) /\
    (forall i,analytic_representative_value (b i) 0 = 0) /\
    @analytic_rotated_germ_ideal R X B hB n e he I g (analytic_germ f) /\
    forall x,analytic_representative_value f x =
      (omega j x)^+k+\sum_(i<k) analytic_representative_value (b i) (P x)*(omega j x)^+(i:nat).
Proof.
move=>hI hProper hBj.
pose A:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
pose Poly:=CommutativePolynomial.space A.
pose embed:=CommutativePolynomial.embed A.
pose variable:=CommutativePolynomial.variable A.
pose coefficient:=@CommutativePolynomial.coefficient A.
have hPoly:=CommutativePolynomial.laws A.
pose E:=@analytic_prefix_germ_map R X NX hNX n e he omega j hJN.
pose Gamma:=@AnalyticCoordinateGerms.value R X NX hNX n e he omega j.
pose J:=@CommutativePolynomialEvaluation.map A Poly G embed variable coefficient hPoly E Gamma.
have hJ:=@CommutativePolynomialEvaluation.laws A Poly G embed variable coefficient hPoly E Gamma.
have [_ [W [k [hK [hDistinguished hMember]]]]]:=
  @analytic_prefix_distinguished_ideal_polynomial R X B hB n e he omega hDual I g j
    Poly embed variable coefficient hPoly J hJ hI hProper hBj.
have hXiBound:=@norm_finite_linear_bounded R X R^o NX (fun z:R^o=>`|z|) hNX
  (@scalar_absolute_value_norm R) n e he (omega j).
have [fXi [hPower hUnused]]:=@weierstrass_functional_power_representative R X NX hNX
  (omega j) 1 hXiBound.
have hXi x:analytic_representative_value fXi x = omega j x by rewrite hPower expr1.
have hGamma:(analytic_germ fXi:G) = Gamma.
  exact:(@AnalyticCoordinateGerms.laws R X NX hNX n e he omega j fXi hXi).
have hJActual:is_commutative_polynomial_evaluation embed variable E (analytic_germ fXi) J.
  by rewrite hGamma.
have [U [b [f [hU0 [hOpen [hAnalytic [hZero [hGerm hValues]]]]]]]]:=
  @distinguished_polynomial_actual_monic R X Y NX NY hNX hNY P E (omega j) fXi
    Poly embed variable coefficient hPoly J W k
    (@analytic_prefix_germ_map_specification R X NX hNX n e he omega j hJN) hXi hJActual hDistinguished.
exists k,U,b,f;split;first exact:hK.
split;first exact:hU0.
split;first exact:hOpen.
split;first exact:hAnalytic.
split;first exact:hZero.
split;last exact:hValues.
by rewrite hGerm.
Qed.
End PreparedEquation.
