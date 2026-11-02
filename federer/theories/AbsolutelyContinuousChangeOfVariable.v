(** Federer (1969), 2.9.21, p. 166: the two change-of-variable formulas for
    a real curve absolutely continuous on [a,b]. the second combines it with
    Federer's 2.5.18(2), p. 112. The weak increasing convention is retained,
    including flat images. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesMonotone
  StieltjesIntegral StieltjesSubstitution RealAbsoluteContinuityUP RealAbsoluteContinuityBasic
  RealAbsoluteContinuityAgreement SegmentRetractionTopology WeightedRealDerivativeIntegrand
  WeightedDerivativeSubsetAgreement AbsolutelyContinuousStieltjesIntegral
  LebesgueContinuousDegenerateIntegral CompactSupportFunctionUP LebesgueScalarMeasure
  SummableRealFunctionUP ExtendedRealOrderTopology MeasureSubsetIntegral
  MeasureIntegralAlmostEquality MeasureAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [absolutely_continuous_monotone_substitution]: direct second
    formula in Federer 2.9.21, p. 166, using 2.5.18(2), p. 112 A
    segment-retracted representative permits application of the earlier
    global-continuity substitution theorem without adding global continuity
    of g to the final statement. Both Lebesgue integrals have the same
    finite value, including when g(a)=g(b). The compact-test hypothesis is
    strengthened to every continuous real f by the already proved cutoff
    argument. *)
Theorem absolutely_continuous_monotone_substitution (R : realType) (g f : R -> R)
    (a b : R) : curve_locally_finite_variation (g : R -> real_line_metric R) ->
  a<b -> is_absolutely_continuous_real_curve g a b ->
  (forall x y : R, x<=y -> g x<=g y) ->
  continuous (f : real_line_metric R -> real_line_metric R) -> exists I : R,
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (weighted_real_curve_derivative_integrand (f \o g) g) I%:E /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[g a,g b]
      (real_total_integrand f) I%:E.
Proof.
move=> hg hab hAC hmono hf.
pose G := g \o @segment_retraction R a b.
have hGfinite := @segment_retracted_curve_locally_finite_variation R g a b hg.
have hGc := @segment_retracted_curve_continuous R g a b (ltW hab)
  (real_absolute_continuity_continuous hAC).
have hGagree x : a<=x -> x<=b -> g x=G x.
  move=> hax hxb; rewrite /G /= segment_retraction_id //; by apply/andP; split.
have hGAC := (@real_absolute_continuity_agree R g G a b hGagree).1 hAC.
have hGmono x y : x<=y -> G x<=G y.
  by move=> hxy; apply: hmono; exact: segment_retraction_monotone hxy.
have hFG : continuous (f \o G : real_line_metric R -> real_line_metric R).
  move=> x; exact: continuous_comp (hGc x) (hf (G x)).
have hI := @absolutely_continuous_stieltjes_integral R G (f \o G) a b hGfinite hab hGAC hFG.
have hId : curve_locally_finite_variation ((fun x : R => x) : R -> real_line_metric R).
  apply: monotone_locally_finite_variation; by move=> x y hxy.
have hValue := @stieltjes_substitution R f G (fun x : R => x) a b hf hGc hGmono hId (ltW hab).
change (stieltjes_integral G (f \o G) a b=stieltjes_integral (fun x : R => x) f (G a) (G b)) in hValue.
have hGa : G a=g a := esym (hGagree a (lexx a) (ltW hab)).
have hGb : G b=g b := esym (hGagree b (ltW hab) (lexx b)).
rewrite hValue hGa hGb in hI.
have hFactor x : a<=x -> x<=b -> (f \o g) x=(f \o G) x.
  by move=> hax hxb; rewrite /= (hGagree x hax hxb).
have hWeight := @weighted_derivative_subset_agreement R (f \o g) (f \o G) g G a b hg hFactor hGagree.
pose I := stieltjes_integral (fun x : R => x) f (g a) (g b).
exists I; split.
- exact (@measure_integral_almost_equal R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ I%:E hI (measure_almost_equal_sym hWeight)).
- exact: lebesgue_continuous_segment_integral_including_diagonal hf (hmono a b (ltW hab)).
Qed.

(** Source for [federer_2_9_21]: complete two formulas in Federer 2.9.21, p.
    166 For every f in K(R), the actual weighted derivative integral equals
    the Stieltjes integral; when g is increasing, the substitution integral
    and its image-interval integral both exist with the same finite value.
    Relative segment continuity is sufficient, and the increasing hypothesis
    is weak, so flat image intervals remain. *)
Theorem federer_2_9_21 (R : realType) (g f : R -> R) (a b : R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) -> a<b ->
  is_absolutely_continuous_real_curve g a b ->
  @compactly_supported_continuous_functions R [the topologicalType of real_line_metric R] f ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (weighted_real_curve_derivative_integrand f g) (stieltjes_integral g f a b)%:E /\
  ((forall x y : R, x<=y -> g x<=g y) -> exists I : R,
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
      (weighted_real_curve_derivative_integrand (f \o g) g) I%:E /\
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[g a,g b]
      (real_total_integrand f) I%:E).
Proof.
move=> hg hab hAC hf; split.
- exact: absolutely_continuous_stieltjes_integral hg hab hAC hf.1.
- move=> hmono; exact: absolutely_continuous_monotone_substitution hg hab hAC hmono hf.1.
Qed.
