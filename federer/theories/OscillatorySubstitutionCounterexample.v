(** Federer (1969), 3.2.7, p. 246: complete
    third counterexample. The printed f is locally
    absolutely continuous and the printed g is summable,
    but their signed substitution formula has no common
    integral value. The unspecified g(0) is set to zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureIntegralAbsolute
  LebesgueScalarMeasure EuclideanLebesgueBoxes SummableRealFunctionUP LocallyAbsolutelyContinuousCurve
  ScalarCurveRemainderNull ScalarAbsoluteContinuousArea ScalarSignedSourceSplitting ScalarSignedMultiplicityAlmost
  ScalarSignedSourceAbsoluteGraph SummableOrientedIndicator ReciprocalRootWeightUP ReciprocalRootWeightBasic
  ReciprocalRootWeightSummable OscillatorySubstitutionCurve OscillatoryWeightAreaDivergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [oscillatory_signed_source_not_summable]:
    failure of source summability in the third
    example of Federer 3.2.7, p. 246.
    A finite signed integral would give a finite
    absolute area integral and contradict the proved
    infinite weighted target upper integral. *)
Theorem oscillatory_signed_source_not_summable (R:realType) (g:R->R):
  is_reciprocal_root_weight g ->
  ~is_measure_summable (@lebesgue_scalar_measure R)
    (scalar_signed_substitution_source (@oscillatory_substitution_curve R) g 0 1).
Proof.
move=>hg hSum; have hm:=lebesgue_scalar_is_measure R.
have [I hAbs]:=measure_summable_absolute_value hm hSum.
have hGraph:=scalar_nonnegative_weight_signed_source_absolute_graph
  (@oscillatory_substitution_curve R) 0 1 (reciprocal_root_weight_nonnegative hg).
have hArea:=measure_integral_graph_equivalent hGraph hAbs.
have hBound:=@real_metric_closed_interval_bounded R 0 1 (@ler01 R).
have hTarget: is_measure_integral (@lebesgue_scalar_measure R)
    (scalar_curve_area_target_integrand (@oscillatory_substitution_curve R) `[0,1] g) I%:E.
  exact ((federer_3_2_6_1_scalar g (@oscillatory_substitution_curve_locally_absolutely_continuous R)
    hBound (lebesgue_scalar_segment_measurable 0 1) I%:E).1 hArea).
have he:=measure_upper_integral_unique (measure_upper_integral_specification _ _) hTarget.2.1.
rewrite (oscillatory_weight_area_target_upper_integral_infinite hg) in he.
discriminate he.
Qed.

(** Source for [federer_3_2_7_3]: the full third
    example of Federer 3.2.7, p. 246.
    The exact printed f and a weight satisfying
    all printed values have the stated regularity,
    the target interval integral is finite, and
    no signed substitution equality exists on [0,1]. *)
Theorem federer_3_2_7_3 (R:realType):
  exists g:R->R,is_reciprocal_root_weight g /\
    is_locally_absolutely_continuous_curve
      (@oscillatory_substitution_curve R:real_line_metric R->real_line_metric R) /\
    is_measure_summable (@lebesgue_scalar_measure R) (real_total_integrand g) /\
    is_measure_summable (@lebesgue_scalar_measure R)
      (scalar_oriented_interval_integrand g (oscillatory_substitution_curve (0:R))
        (oscillatory_substitution_curve (1:R))) /\
    ~exists z : \bar R,
      is_measure_integral (@lebesgue_scalar_measure R)
        (scalar_signed_substitution_source (@oscillatory_substitution_curve R) g 0 1) z /\
      is_measure_integral (@lebesgue_scalar_measure R)
        (scalar_oriented_interval_integrand g (oscillatory_substitution_curve (0:R))
          (oscillatory_substitution_curve (1:R))) z.
Proof.
have [g hg]:=reciprocal_root_weight_exists R.
have hSum:=reciprocal_root_weight_summable hg.
have hTarget:=summable_oriented_indicator
  (oscillatory_substitution_curve (0:R)) (oscillatory_substitution_curve (1:R)) hSum.
exists g; split=>//; split; first exact:oscillatory_substitution_curve_locally_absolutely_continuous.
split=>//; split=>//.
move=>[z [hSource hRight]].
have [a ha]:=hTarget.
have he:z=a%:E:=measure_integral_unique hRight ha.
apply:(oscillatory_signed_source_not_summable hg); exists a; by rewrite -he.
Qed.
