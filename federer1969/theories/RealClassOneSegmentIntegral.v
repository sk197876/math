(** Federer (1969), 4.1.7, p. 359:
    integrate the derivative of an original
    scalar test on a finite interval.
    Reuse the proved fundamental theorem of
    3.1.11, pp. 220–221, and the scalar
    Lebesgue/Riemann identification of 2.5.17,
    p. 111. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP RealMetricBackground NormMetric NormClassOneUP NormClassZeroTopology
  NormDifferentialUP NormHigherCurveDerivativeUP NormedCurveFundamentalTheorem
  NormedStieltjesLaws NormedStieltjesUnique StieltjesLebesgueInduced
  LebesgueContinuousDegenerateIntegral LocalUniquenessExample LebesgueScalarMeasure
  MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [real_class_one_segment_integral]:
    the original finite interval integral of
    D equals F(b)-F(a), supporting the
    two actual primitives in Federer 4.1.7,
    p. 359. Degenerate intervals are
    retained and the differential is actual. *)
Theorem real_class_one_segment_integral (R:realType) (F D:R->R) a b:
  a<=b ->
  (forall t,has_norm_differential (fun s:R^o=>`|s|) (fun s:R^o=>`|s|) (fun _=>True)
    F t (@scalar_coefficient_linear_map R R^o (D t))) ->
  norm_class_zero (fun s:R^o=>`|s|) (fun s:R^o=>`|s|) (fun _=>True) D ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (real_total_integrand D) (F b-F a)%:E.
Proof.
move=>hab hDifferential hD.
pose N:=fun s:R^o=>`|s|.
pose hN:=@scalar_absolute_value_norm R.
have hFTC:=@normed_curve_fundamental_theorem R R^o N hN (fun _=>True) F D a b hab
  (fun _ _=>Logic.I) (fun t _=>hDifferential t) hD.
have hContinuous:continuous (D:real_line_metric R->real_line_metric R).
  move=>t.
  have hMap:=@norm_class_zero_continuous_at R R^o R^o N N hN hN (fun _=>True) D t hD Logic.I.
  exact:(continuous_comp (continuous_comp (@scalar_line_to_norm_continuous R t) hMap)
    (@scalar_norm_to_line_continuous R (D t))).
have hRS:=normed_stieltjes_scalar_agreement (@identity_locally_finite_variation R) hContinuous hab.
have hValue:=normed_stieltjes_integral_unique hN hFTC hRS.
have hLeb:=lebesgue_continuous_segment_integral_including_diagonal hContinuous hab.
by rewrite -hValue in hLeb.
Qed.
