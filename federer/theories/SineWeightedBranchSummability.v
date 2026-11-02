(** Federer (1969), 3.2.7, p. 246:
    if the printed sine-weighted source integrand were
    measurable, its bounded principal-branch restriction
    would be summable. The first identity of 3.2.6
    will then recover measurability of the original set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology RealTrigonometryUP RealTrigonometrySealed
  SineMultiplicity ScalarAbsoluteContinuousArea ScalarSignedSourceSplitting ScalarSignedPieceIntegrals
  PartialFunctionUP PartialZeroExtension CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableGraphEquivalence MeasurableZeroExtension
  BoundedSubsetSummability MeasureIntegralUP LebesgueScalarMeasure BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sine_branch_source_summable_of_measurable]:
    supporting bounded single-branch argument for the
    first example in Federer 3.2.7, p. 246.
    Boundedness of the real weight is a helper
    hypothesis satisfied by the printed g= 1+c. *)
Theorem sine_branch_source_summable_of_measurable (R:realType) (g:R->R) (M:R):
  0<=M -> (forall y,`|g y|<=M) ->
  is_measure_measurable_function (@lebesgue_scalar_measure R)
    (scalar_curve_area_source_integrand (@RealTrigonometry.sine R) setT g) ->
  is_measure_summable (@lebesgue_scalar_measure R)
    (scalar_curve_area_source_integrand (@RealTrigonometry.sine R) ((@sine_principal_source_interval R)) g).
Proof.
move=>hM hBound hFull; have hm:=lebesgue_scalar_is_measure R.
pose S:=@RealTrigonometry.sine R; pose C:=@RealTrigonometry.cosine R.
pose p:=@RealTrigonometry.half_period R; pose T:=(@sine_principal_source_interval R).
have ht:=@RealTrigonometry.laws R.
have hT:measure_measurable (@lebesgue_scalar_measure R) T.
  exact (borel_regular_borel_measurable hm (lebesgue_scalar_borel_regular R)
    (closed_borel_set (@segment_closed_real R (-(p/2)) (p/2)))).
have hOrder:-(p/2)<=p/2 by have hp:0<p:=real_trigonometry_pi_positive ht; lra.
have hFinite:(lebesgue_scalar_measure T< +oo)%E.
  rewrite /T /sine_principal_source_interval (lebesgue_scalar_segment hOrder); exact:ltry.
have hCut:=@measurable_zero_extension R [the choiceType of real_line_metric R]
  (extended_real_line R) (@lebesgue_scalar_measure R) hm 0 T
  (scalar_curve_area_source_integrand S setT g) hT hFull.
have hSource:=measurable_function_graph_equivalent
  (@scalar_area_source_subset_graph R S g T setT (subsetT T)) hCut.
pose chi:=@CharacteristicFunction.value R [the choiceType of real_line_metric R] T.
have hChi:is_characteristic_function T chi:=@CharacteristicFunction.laws R [the choiceType of real_line_metric R] T.
apply:(@bounded_supported_partial_summable R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) _ T chi M hm hT hFinite hChi hM hSource).
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ (measure_almost_everywhere_true hm))=>x _.
case:(pselect (T x))=>hx.
- exists (g (S x) * `|C x|); split.
  + exact (scalar_area_source_actual_value g (real_sine_derivative ht x) hx).
  + rewrite (characteristic_on_set hChi hx) mulr1 normrM (ger0_norm (normr_ge0 (C x))).
    apply:le_trans (ler_wpM2r (normr_ge0 (C x)) (hBound (S x))) _.
    have hh:=ler_wpM2l hM (real_cosine_bound ht x); by rewrite mulr1 in hh.
- exists 0; split; first exact (@scalar_area_source_off R S g T x hx).
  by rewrite normr0 (characteristic_off_set hChi hx) mulr0.
Qed.
