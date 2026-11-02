(** Federer (1969), 2.9.24, p. 169: if f has finite variation on [a,b] and g
    is absolutely continuous there, integral f g' dL1 plus integral g df is
    the boundary product difference. Retractions supply proof
    representatives without assumptions outside the interval, and bounded
    convergence uses the printed right-endpoint step functions. its
    finite-sum endpoint misprint is documented separately in
    IntegrationByPartsFiniteIdentity.v. The local Federer erratum has no
    entry for this formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  FiniteIntervalVariationLocalization AbsoluteContinuityFiniteVariation
  RealAbsoluteContinuityUP RealAbsoluteContinuityBasic RealAbsoluteContinuityAgreement
  SegmentRetractionTopology StieltjesSums StieltjesIntegral StieltjesSubstitution
  StieltjesContinuityPoints StieltjesZeroWidthIntegral WeightedRealDerivativeIntegrand
  WeightedDerivativeSubsetAgreement MeasureUP MeasureIntegralAlmostEquality MeasureSubsetIntegral
  LebesgueScalarMeasure NullSubsetIntegral BVACIntegrationByParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_9_24]: complete integration-by-parts formula of
    Federer 2.9.24, p. 169. The actual finite subset integral equals
    f(b)g(b)-f(a)g(a)-integral g df. Only the printed local variation and
    absolute-continuity hypotheses are imposed, and a=b is included. *)
Theorem federer_2_9_24 (R : realType) (f g : R -> R) (a b : R) :
  a<=b -> (curve_variation (f : R -> real_line_metric R) a b < +oo)%E ->
  is_absolutely_continuous_real_curve g a b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (weighted_real_curve_derivative_integrand f g)
    (f b*g b-f a*g a-stieltjes_integral f g a b)%:E.
Proof.
move=> hAB hV hAC; case: (ltP a b)=> hab.
- pose c := @segment_retraction R a b.
  pose F := f \o c.
  pose G := g \o c.
  have hF x : a<=x -> x<=b -> F x=f x.
    move=> hax hxb; rewrite /F /c /= segment_retraction_id //; by apply/andP; split.
  have hG x : a<=x -> x<=b -> G x=g x.
    move=> hax hxb; rewrite /G /c /= segment_retraction_id //; by apply/andP; split.
  have hFbv := @finite_interval_retracted_curve_variation R f a b hAB hV.
  have hGbv := @absolutely_continuous_retracted_curve_variation R g a b hAB hAC.
  have hGc := @segment_retracted_curve_continuous R g a b hAB
    (real_absolute_continuity_continuous hAC).
  have hAgree x : a<=x -> x<=b -> g x=G x by move=> hax hxb; exact: esym (hG x hax hxb).
  have hGAC := (@real_absolute_continuity_agree R g G a b hAgree).1 hAC.
  have [M [hM hbound]] := @finite_interval_curve_value_bound R f a b hAB hV.
  have hFbound x : `|F x|<=M.
    have /andP[hlo hhi] := @segment_retraction_bounds R a b x hAB.
    exact: hbound _ hlo hhi.
  have hi := @bounded_bv_ac_integration_by_parts R F G a b M
    hFbv hGbv hGc hab hGAC hM hFbound.
  have hSt : stieltjes_integral F G a b=stieltjes_integral f g a b.
    rewrite (@stieltjes_integral_eq_on R G F f a b hAB); last first.
      move=> x /andP[hax hxb]; exact: hF x hax hxb.
    apply: (@stieltjes_integral_eq_on_integrand R f G g a b hAB)=> x /andP[hax hxb].
    exact: hG x hax hxb.
  rewrite (hF b hAB (lexx _)) (hG b hAB (lexx _))
    (hF a (lexx _) hAB) (hG a (lexx _) hAB) hSt in hi.
  have hEq := @weighted_derivative_subset_agreement R F f G g a b hGbv hF hG.
  exact (@measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ _ hi hEq).
- have heq : a=b by apply/eqP; rewrite eq_le hAB hab.
  subst b; rewrite stieltjes_integral_zero_width !subrr.
  apply: (@null_target_subset_integral R (real_line_metric R) (@lebesgue_scalar_measure R)
    (weighted_real_curve_derivative_integrand f g) `[a,a] (lebesgue_scalar_is_measure R)).
  by rewrite lebesgue_scalar_segment ?lexx // subrr.
Qed.
