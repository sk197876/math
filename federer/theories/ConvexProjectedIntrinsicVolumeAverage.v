(** Federer (1969), 3.2.35, p. 272:
    repeated projection volume averaging in the
    dimension induction, including all zero degrees. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionComposition EuclideanLebesgueDimensions
  EuclideanProjectionConvexImage EuclideanProjectionBoundedImage ProjectionCompositeVolumeIntegral
  ConvexProjectedVolumeContinuity ConvexIntrinsicVolumeIntegrals ProjectedVolumeMeasurability
  IntegralGeometricGauge ProjectionBeta OrthogonalProjectionProbability ExtendedRealOrderTopology
  PartialFunctionBasic PartialExtendedOrderLoci PartialProductSections ParameterizedIntegral
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureNonnegativeIntegral PositiveCharacteristicMeasurability CountablyMeasurableUP
  CountablyMeasurableBasic CountablyMeasurableFunctions CountablyMeasurableNullModification CountablyMeasurableProduct ProductMeasure
  ProductBorelRegularity ProductFunctionFubini MetricProductBackground MetricProductSeparability
  TopologicalBorel BorelRegularMeasureUP SeparableMetricBaseSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_projected_intrinsic_volume_average]:
    the repeated theta averages in the last
    display of Federer 3.2.35, p. 272.
    Both actual orders of integration are justified
    by the proved Borel composite-volume function
    and Fubini. The fixed-left marginal gives
    beta_1(n,m) zeta^m(S); each fixed-right section
    gives beta_1(k,m) zeta^m(p(S)). All original
    source hypotheses and all natural degrees
    remain, with no assumed integral or selected
    independent projection frame. *)
Theorem convex_projected_intrinsic_volume_average (R:realType) n k m
    (hkn:(k<=n)%N) (hmk:(m<=k)%N)
    (C:orthogonal_projection_metric_space R k m*orthogonal_projection_metric_space R n k->
      orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_euclidean_projection_composition C ->S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  is_measure_integral (@orthogonal_projection_probability R n k hkn)
    (partial_function_total (fun p=>((@projection_beta R k m hmk 1)%:E*
      @integral_geometric_gauge R k m hmk 1 (euclidean_projection_linear p @` S):extended_real_line R)))
    ((@projection_beta R n m (leq_trans hmk hkn) 1)%:E*
      @integral_geometric_gauge R n m (leq_trans hmk hkn) 1 S).
Proof.
move=>hC hNonempty hS hBound.
pose Q:=orthogonal_projection_metric_space R k m.
pose P:=orthogonal_projection_metric_space R n k.
pose Z:=[the metricType R of metric_product Q P].
pose alpha:=@orthogonal_projection_probability R k m hmk.
pose beta:=@orthogonal_projection_probability R n k hkn.
pose ha:=@theta_star_is_measure R k m hmk.
pose hb:=@theta_star_is_measure R n k hkn.
pose mu:=product_measure ha hb.
have hm:=product_measure_is_measure ha hb.
have [Dq [hDq hdq]]:=orthogonal_projection_metric_separable R k m.
have [Dp [hDp hdp]]:=orthogonal_projection_metric_separable R n k.
pose U:=@SeparableMetricBase.value R Q Dq hDq hdq.
pose V:=@SeparableMetricBase.value R P Dp hDp hdp.
have hRegular:=@product_measure_borel_regular R Q P alpha beta ha hb U V
  (@SeparableMetricBase.laws R Q Dq hDq hdq) (@SeparableMetricBase.laws R P Dp hDp hdp)
  (@theta_star_borel_regular R k m hmk) (@theta_star_borel_regular R n k hkn).
have hQA:measure_countably_measurable alpha setT.
  apply:finite_measurable_set_countably_measurable; first exact:measure_measurable_whole ha.
  by rewrite /alpha theta_star_total; exact:ltry.
have hPB:measure_countably_measurable beta setT.
  apply:finite_measurable_set_countably_measurable; first exact:measure_measurable_whole hb.
  by rewrite /beta theta_star_total; exact:ltry.
have hWhole:=@product_whole_countably_measurable R Q P alpha beta ha hb hQA hPB.
pose f:=partial_function_total (fun z:Q*P=>projected_volume_function S (C z)).
have hMeasurable:=@convex_projected_volume_parameter_measurable R n m Z mu C S hm hRegular
  (@euclidean_projection_composition_continuous R n k m C hC) hNonempty hS hBound.
have hPositive:measure_almost_everywhere mu (partial_extended_nonnegative_locus f).
  apply:(@measure_almost_everywhere_mono R (Q*P)%type mu hm setT _ _ (measure_almost_everywhere_true hm))=>z _.
  exists (projected_volume_function S (C z)); split; first reflexivity.
  exact:projected_volume_function_nonnegative.
have [hIntegral _]:=@nonnegative_measurable_function_integral R (Q*P)%type mu hm f hMeasurable hPositive.
pose K:=measure_lower_integral mu f.
have hCount:=@countably_measurable_function_on_countable_source R (Q*P)%type (extended_real_line R)
  mu hm 0 f (@extended_real_zero_closed R) hWhole hMeasurable.
have [hOuterQ hOuterP]:=@product_function_fubini R Q P alpha beta ha hb f K hIntegral hCount.
pose J:=(@projection_beta R n m (leq_trans hmk hkn) 1)%:E*
  @integral_geometric_gauge R n m (leq_trans hmk hkn) 1 S.
have hFixed q:is_measure_integral beta
    (partial_function_total (fun p=>projected_volume_function S (C (q,p)))) J.
  exact:(@projection_composite_volume_fixed_left_integral R n k m hkn hmk C S q hC hNonempty hS hBound).
have hConstant:is_measure_integral alpha (partial_function_total (fun _:Q=>(J:extended_real_line R))) K.
  apply:(measure_integral_graph_equivalent _ hOuterQ)=>q z.
  rewrite parameterized_integral_specification.
  change (is_measure_integral beta (partial_function_total (fun p=>projected_volume_function S (C (q,p)))) z <->J=z).
  split; first by move=>hz; exact:Logic.eq_sym (measure_integral_unique hz (hFixed q)).
  by move=> <-; exact:hFixed.
have hJPositive:0<=J.
  change (0<=(@projection_beta R n m (leq_trans hmk hkn) 1)%:E*
    @integral_geometric_gauge R n m (leq_trans hmk hkn) 1 S).
  apply:mule_ge0.
  - rewrite lee_fin; exact:ltW (@projection_beta_positive R n m (leq_trans hmk hkn) 1 (lexx 1)).
  - exact:(@convex_intrinsic_volume_nonnegative_finite R n m (leq_trans hmk hkn) 1 S
      hNonempty hS hBound (lexx 1)).1.
have hConstantValue:=@nonnegative_extended_constant_integral R Q alpha ha J hJPositive.
rewrite /alpha theta_star_total mule1 in hConstantValue.
have hValue:K=J:=measure_integral_unique hConstant hConstantValue.
rewrite hValue in hOuterP.
apply:(measure_integral_graph_equivalent _ hOuterP)=>p z.
rewrite parameterized_integral_specification.
pose T:=euclidean_projection_linear p @` S.
have hTNonempty:T!=set0 by have [a haS]:=hNonempty; exists (euclidean_projection_linear p a); by exists a.
have hTConvex:=@euclidean_projection_convex_image R n k p S hS.
have hTBound:=@euclidean_projection_bounded_image R n k p S hBound.
have hSection:=@convex_intrinsic_volume_integral R k m hmk T hTNonempty hTConvex hTBound.
have hImages q:euclidean_projection_linear q @` (euclidean_projection_linear p @` S)=
    euclidean_projection_linear (C (q,p)) @` S.
  apply/seteqP; split=>y.
  - move=>[x [a haS <-] <-]; exists a=>//; exact:hC q p a.
  - move=>[a haS <-]; exists (euclidean_projection_linear p a).
    + by exists a.
    + exact:Logic.eq_sym (hC q p a).
have hFunction:projected_volume_function (m:=m) T=
    (fun q:Q=>projected_volume_function S (C (q,p))).
  apply:funext=>q; by rewrite /projected_volume_function /T (hImages q).
rewrite hFunction in hSection.
change (is_measure_integral alpha (partial_function_total (fun q=>projected_volume_function S (C (q,p)))) z <->
  (@projection_beta R k m hmk 1)%:E*@integral_geometric_gauge R k m hmk 1 T=z).
split; first by move=>hz; exact:Logic.eq_sym (measure_integral_unique hz hSection).
by move=> <-; exact hSection.
Qed.
