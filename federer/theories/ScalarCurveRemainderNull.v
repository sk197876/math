(** Federer (1969), 3.2.6, p. 246: the
    image of the exact remainder A_3 has scalar Lebesgue
    measure zero. Actual zero derivatives and undefined
    derivatives are treated separately by the conull domain
    and both interval endpoints are retained in A_3. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology RealCurveDerivativeUP
  RealCurveDerivativeIntegrands RealDerivativeRepresentative LocallyAbsolutelyContinuousCurve ScalarCurveDerivativeLoci
  ScalarAbsoluteContinuousArea PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialDensityProduct
  MetricDiameterUP MetricDiameter CoveringFamilyUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureConullZeroIntegral NullMultiplicityIntegral LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_metric_closed_interval_bounded]: supporting
    bounded source interval in Federer 3.2.6, p. 245,
    directly from its abstract diameter laws. *)
Lemma real_metric_closed_interval_bounded (R:realType) (a b:R):
  (a<=b)%R -> metric_set_bounded (`[a,b]:set (real_line_metric R)).
Proof.
move=>hab.
have hBound:extended_metric_diameter (`[a,b]:set (real_line_metric R))<=(b-a)%:E.
  apply:(metric_diameter_least (extended_metric_diameter_specification (`[a,b]:set (real_line_metric R)))).
  - by rewrite lee_fin subr_ge0.
  - move=>x y hx hy; move:hx hy; rewrite /= !in_itv /= =>/andP[hax hxb] /andP[hay hyb].
    rewrite lee_fin real_line_metric_distanceE ler_norml; apply/andP; split; lra.
exact (le_lt_trans hBound (ltry _)).
Qed.

(** Source for [scalar_remainder_absolute_derivative_zero]:
    the speed is zero almost everywhere on A_3 in
    Federer 3.2.6, p. 246. The derivative remains
    undefined at its genuine exceptional points; those and
    the two endpoints are removed only in the almost assertion. *)
Lemma scalar_remainder_absolute_derivative_zero (R:realType) (f:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x|
    partial_function_graph (partial_function_zero_extension (0:extended_real_line R)
      (scalar_nonsigned_derivative_remainder f a b) (real_curve_absolute_derivative_integrand f)) x 0].
Proof.
move=>hAC; have hm:=lebesgue_scalar_is_measure R.
have hD:=bv_real_derivative_representative_ae (locally_absolutely_continuous_curve_finite_variation hAC).
pose E:=[set a] `|` [set b].
have hE:lebesgue_scalar_measure E=0.
  exact (measure_null_union hm (lebesgue_scalar_singleton a) (lebesgue_scalar_singleton b)).
have hOff:measure_almost_everywhere (@lebesgue_scalar_measure R) (~` E).
  by rewrite /measure_almost_everywhere setCK.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ (measure_almost_everywhere_and hm hD hOff))=>x [hDx hxE].
case:(pselect (scalar_nonsigned_derivative_remainder f a b x))=>hx.
- have hxA:=(hx.1); move:hxA; rewrite /= in_itv /= =>/andP[hax hxb].
  have hxa:x!=a by apply/eqP=>he; apply:hxE; left; exact he.
  have hxb0:x!=b by apply/eqP=>he; apply:hxE; right; exact he.
  have hax':(a<x)%R by rewrite lt_neqAle eq_sym hxa hax.
  have hxb':(x<b)%R by rewrite lt_neqAle hxb0 hxb.
  have hInside:(`]a,b[:set (real_line_metric R)) x by rewrite /= in_itv /= hax' hxb'.
  pose v:=real_derivative_representative f x.
  have hPos:~(0<v)%R.
    move=>hv; apply:hx.2; left; split; first exact hInside.
    exists v; by split.
  have hNeg:~(v<0)%R.
    move=>hv; apply:hx.2; right; split; first exact hInside.
    exists v; by split.
  have hvLe:(v<=0)%R by rewrite leNgt; exact/negP.
  have hvGe:(0<=v)%R by rewrite leNgt; exact/negP.
  have hv0:v=0%R by apply/eqP; rewrite eq_le hvLe hvGe.
  apply/partial_function_zero_extension_graph; left; split; first exact hx.
  exists v; split; first exact hDx.
  by rewrite hv0 normr0.
- apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [scalar_nonsigned_remainder_image_null]: the
    assertion N(f|A_3,y)=0 almost everywhere in Federer
    3.2.6, p. 246, stated equivalently as nullity
    of its whole represented image, by the constant-weight
    case of the first equation. *)
Theorem scalar_nonsigned_remainder_image_null (R:realType) (f:R->R) (a b:R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) -> (a<b)%R ->
  lebesgue_scalar_measure (f @` scalar_nonsigned_derivative_remainder f a b)=0.
Proof.
move=>hAC hab; have hm:=lebesgue_scalar_is_measure R.
pose A:=scalar_nonsigned_derivative_remainder f a b.
have hA:measure_measurable (@lebesgue_scalar_measure R) A:=
  (scalar_derivative_interval_sets_measurable a b hAC).2.2.
have hBound:metric_set_bounded A.
  apply:le_lt_trans (@extended_metric_diameter_mono R [the metricType R of real_line_metric R]
    A `[a,b] (fun x hx=>hx.1)) _.
  exact (real_metric_closed_interval_bounded (ltW hab)).
have hZero:=scalar_remainder_absolute_derivative_zero a b hAC.
have hSource:is_measure_integral (@lebesgue_scalar_measure R)
    (scalar_curve_area_source_integrand f A (fun _=>1%R)) 0.
  apply:(measure_almost_zero_integral hm).
  apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm _ _ _ hZero)=>x hx.
  case:(pselect (A x))=>hAx.
  - have hAbs:=(partial_function_zero_extension_on _ _ _ hAx).1 hx.
    apply/partial_function_zero_extension_graph; left; split; first exact hAx.
    apply/partial_density_product_graph; exists 1,0; split=>//; split=>//; exact:mule0.
  - apply/partial_function_zero_extension_graph; right; by split.
have hTarget:=(federer_3_2_6_1_scalar (fun _=>1%R) hAC hBound hA 0).1 hSource.
apply:(null_multiplicity_integral_image_null hm).
apply:(@measure_integral_graph_equivalent R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) _ _ _ _ hTarget)=>y z.
change (1*@MappingMultiplicity.mapping_multiplicity R _ _ f A y=z <->
  @MappingMultiplicity.mapping_multiplicity R _ _ f A y=z).
by rewrite mul1e.
Qed.
