(** Federer (1969), 3.2.7, p. 246:
    the full sine and the weight one plus a nonmeasurable
    characteristic function. The target integral is infinity,
    whereas the actual weighted source is nonmeasurable.
    The bounded principal branch proves the latter by 3.2.6. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology RealTrigonometryUP RealTrigonometrySealed
  RealTrigonometryBasic SineMultiplicity BoundedScalarNonmeasurableSubset SineWeightedBranchSummability
  InfiniteMultiplicityWeightIntegral ShiftedCharacteristicMeasurability ScalarAbsoluteContinuousArea ScalarCurveRemainderNull
  PartialFunctionUP PartialFunctionBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasurableFunctionUP MeasurableGraphEquivalence MeasureIntegralUP LebesgueScalarMeasure
  BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_7_1]: the complete first
    counterexample of Federer 3.2.7, p. 246,
    in the scalar carrier of R^1. The sine is
    nonexpanding and locally absolutely continuous by the
    preceding proved laws. B and its characteristic
    function are actual existence witnesses. *)
Theorem federer_3_2_7_1 (R:realType):
  exists (B:set (real_line_metric R)) (c:R->R),
    B `<=` (`[(-1)%R,1%R]:set (real_line_metric R)) /\
    is_characteristic_function B c /\ ~measure_measurable (@lebesgue_scalar_measure R) B /\
    is_measure_integral (@lebesgue_scalar_measure R)
      (scalar_curve_area_target_integrand (@RealTrigonometry.sine R) setT (fun y=>1+c y)) (+oo)%E /\
    ~is_measure_measurable_function (@lebesgue_scalar_measure R)
      (scalar_curve_area_source_integrand (@RealTrigonometry.sine R) setT (fun y=>1+c y)).
Proof.
have [B [hBI hNot]]:=@bounded_scalar_nonmeasurable_subset R.
pose c:=@CharacteristicFunction.value R [the choiceType of real_line_metric R] B.
have hc:is_characteristic_function B c:=@CharacteristicFunction.laws R [the choiceType of real_line_metric R] B.
pose g:=fun y=>1+c y.
pose S:=@RealTrigonometry.sine R.
have hBounds:=shifted_characteristic_positive_bounded hc.
have hRight:is_measure_integral (@lebesgue_scalar_measure R)
    (scalar_curve_area_target_integrand S setT g) (+oo)%E.
  apply:(@positive_weight_infinite_multiplicity_integral R S g).
  - exact (@real_sine_full_multiplicity R).
  - exact (@real_sine_no_fibre_off_unit_interval R setT).
  - move=>y _ _; exact (lt_le_trans (@ltr01 R) (hBounds y).1).
exists B,c; split; first exact hBI; split; first exact hc; split; first exact hNot.
split; first exact hRight.
move=>hMeas.
have hBound y:`|g y|<= 2.
  rewrite (ger0_norm (le_trans (@ler01 R) (hBounds y).1)); exact (hBounds y).2.
have [j hj]:=@sine_branch_source_summable_of_measurable R g 2 (ler0n R 2) hBound hMeas.
pose T:=(@sine_principal_source_interval R); pose p:=@RealTrigonometry.half_period R.
have hOrder:-(p/2)<=p/2 by have hp:0<p:=real_trigonometry_pi_positive (@RealTrigonometry.laws R); lra.
have hT:measure_measurable (@lebesgue_scalar_measure R) T.
  exact (borel_regular_borel_measurable (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)
    (closed_borel_set (@segment_closed_real R (-(p/2)) (p/2)))).
have hTBound:=real_metric_closed_interval_bounded hOrder.
have hTarget:=(federer_3_2_6_1_scalar g (@real_sine_locally_absolutely_continuous R) hTBound hT j%:E).1 hj.
pose chi:=@CharacteristicFunction.value R [the choiceType of real_line_metric R]
  (`[(-1)%R,1%R]:set (real_line_metric R)).
have hChi:is_characteristic_function (`[(-1)%R,1%R]:set (real_line_metric R)) chi:=
  @CharacteristicFunction.laws R [the choiceType of real_line_metric R] (`[(-1)%R,1%R]:set (real_line_metric R)).
have hTotal:is_measure_measurable_function (@lebesgue_scalar_measure R)
    (partial_function_total (fun y=>(((1+c y)*chi y)%:E:extended_real_line R))).
  apply:(measurable_function_graph_equivalent _ hTarget.1)=>y z.
  change ((((1+c y)%:E * @MappingMultiplicity.mapping_multiplicity R
    [the choiceType of real_line_metric R] R S T y)%E)=z <-> ((1+c y)*chi y)%:E=z).
  by rewrite (@real_sine_principal_branch_multiplicity R chi hChi y) -EFinM.
exact (hNot (shifted_characteristic_cutoff_requires_measurable hBI hc hChi hTotal)).
Qed.
