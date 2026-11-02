(** Federer (1969), 2.9.21, p. 166: the integral of f dg equals the Lebesgue
    integral of f g' on an absolutely continuous segment. The core proof
    combines the induced measures, 2.9.7 and 2.4.10. A segment retraction
    removes temporary global continuity assumptions; a compact cutoff
    extends the printed compact-test statement to all continuous real
    integrands. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesImageMeasures
  RealAbsoluteContinuityUP RealAbsoluteContinuityBasic RealAbsoluteContinuityAgreement
  SegmentRetractionTopology StieltjesSubstitution StieltjesContinuityPoints StieltjesIntegral
  LebesgueRiemannSegment CompactSupportFunctionUP CompactSupportFunctionLattice
  WeightedRealDerivativeIntegrand WeightedDerivativeSubsetAgreement ContinuousStieltjesDerivativeDensity
  ExtendedRealOrderTopology MeasureSubsetIntegral MeasureIntegralAlmostEquality
  MeasureAlmostEquality LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [absolutely_continuous_stieltjes_integral]: direct first
    identity of Federer 2.9.21, p. 166 The theorem is strengthened from f in
    K(R) to every continuous real f by the already proved compact cutoff
    agreeing on [a,b]. The curve is only relatively continuous there:
    retraction gives a globally continuous proof representative, and
    null-endpoint derivative agreement transfers the result back to the
    original partial derivative. *)
Theorem absolutely_continuous_stieltjes_integral (R : realType) (g f : R -> R)
    (a b : R) : curve_locally_finite_variation (g : R -> real_line_metric R) ->
  a<b -> is_absolutely_continuous_real_curve g a b ->
  continuous (f : real_line_metric R -> real_line_metric R) ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (weighted_real_curve_derivative_integrand f g) (stieltjes_integral g f a b)%:E.
Proof.
move=> hg hab hAC hf.
pose G := g \o @segment_retraction R a b.
have hGfinite := @segment_retracted_curve_locally_finite_variation R g a b hg.
have hGcontinuous := @segment_retracted_curve_continuous R g a b (ltW hab)
  (real_absolute_continuity_continuous hAC).
have hGagree x : a<=x -> x<=b -> g x=G x.
  move=> hax hxb; rewrite /G /= segment_retraction_id //.
  by apply/andP; split.
have hGAC := (@real_absolute_continuity_agree R g G a b hGagree).1 hAC.
have [psip [psim hp]] := @induced_measure_pair_exists R G hGfinite.
have [F [hF hFagree]] := @continuous_segment_compact_extension R f a b hf.
have hInt := @continuous_stieltjes_derivative_density R G F psip psim a b
  hGfinite hp hab hGcontinuous hGAC hF.
have hValue : stieltjes_integral G F a b=stieltjes_integral g f a b.
  rewrite (@stieltjes_integral_eq_on R F G g a b (ltW hab)); last first.
    move=> x /andP[hax hxb]; exact: esym (hGagree x hax hxb).
  exact: stieltjes_integral_eq_on_integrand (ltW hab) hFagree.
have hFactor x : a<=x -> x<=b -> f x=F x.
  move=> hax hxb; apply: esym; apply: hFagree; by apply/andP; split.
have hWeight := @weighted_derivative_subset_agreement R f F g G a b hg hFactor hGagree.
rewrite hValue in hInt.
exact (@measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ (stieltjes_integral g f a b)%:E hInt
  (measure_almost_equal_sym hWeight)).
Qed.
