(** Federer (1969), 3.2.46, p. 282: actual
    counted area for maps Lipschitz in the original
    Riemannian path distances. Proved local coordinate
    extensions, exact differential agreement and countable
    source partitioning remove the temporary global Euclidean
    Lipschitz premise from the coordinate theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RiemannianTensorUP RiemannianMetricCarrier
  RiemannianPathLipschitz RiemannianChartReference RiemannianChartLift RiemannianHausdorff
  RiemannianMapJacobian RiemannianLinearJacobian RiemannianMapJacobianLocal
  RiemannianMapAreaJacobianMeasurable RiemannianTargetJacobian RiemannianCoordinateArea
  RiemannianReferenceSetImage RiemannianReferenceSubsetIntegral
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourcePostcomposition
  PartialExtendedOrderLoci MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureDensityUP MeasureDensity MeasureDensityMeasurable DensityCharacteristicIntegral
  MeasureSubsetIntegral MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence MeasureStepIntegralIdentification
  MeasurableFunctionUP MeasurableRealEmbedding MeasureLocalCountedArea
  BorelRegularMeasureUP TopologicalBorel MappingMultiplicity MappingChartMultiplicity
  LipschitzUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_reference_area_formula]:
    actual area against the ordinary source-coordinate
    reference measure, supporting 3.2.46, p. 282.
    The original map is Lipschitz only for its actual
    Riemannian path distances. Every completed measurable
    source subset, all natural dimensions, infinite fibre
    counts and infinite integral values are retained.
    This is the unweighted identity; signed alternatives
    and the coarea assertion are separate obligations. *)
Theorem riemannian_map_reference_area_formula (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg)) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (@riemannian_chart_reference R m A g hg) S ->
  exists a,
    is_measure_subset_integral (@riemannian_chart_reference R m A g hg) S
      (partial_real_function_embed (riemannian_map_euclidean_source_jacobian f m)) a /\
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp)
      (partial_function_total (fun y=>(@mapping_multiplicity R _ _ f S y : extended_real_line R))) a.
Proof.
move=> hLip hS.
pose X := [the topologicalType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose phi := @riemannian_chart_reference R m A g hg.
pose J := partial_real_function_embed (riemannian_map_euclidean_source_jacobian f m).
pose nu := measure_with_density phi J.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hPhi := @riemannian_chart_reference_is_measure R m A g hg.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
have hJReal := @riemannian_map_coordinate_area_jacobian_measurable R m n A B g h hg hh f hLip.
have hJMeas := @measurable_partial_real_embedding R X phi hPhi
  (riemannian_map_euclidean_source_jacobian f m) hJReal.
have hJPositive : measure_almost_everywhere phi (partial_extended_nonnegative_locus J).
  apply: (@measure_almost_everywhere_mono R X phi hPhi _ _ _
    (measurable_function_domain hJReal))=> x [j hj].
  exists j%:E; split; first by exists j; split.
  have [D [hD hValue]] := hj.
  rewrite lee_fin -hValue; exact: riemannian_linear_jacobian_nonnegative.
have hNu := measure_with_density_is_measure hPhi hJPositive.
have [C hBase] := @riemannian_chart_countable_open_base R m A g hg.
have hTarget : is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f S y : extended_real_line R))) (nu S).
  apply: (@measure_local_counted_area R X Y phi nu beta f C hPhi hNu hBeta hBase _ _ S hS).
  - move=> D hD.
    have hDMeas := @riemannian_chart_reference_borel_measurable R m A g hg D hD.
    split; first exact hDMeas.
    exact (@measure_with_density_measurable R X phi hPhi J D hJPositive hDMeas).
  - move=> a.
    have [U [K [F [hU [hUa [hUA [hK [hBound [hRange hAgreement]]]]]]]]] :=
      @riemannian_path_map_local_coordinates R m n A B g h hg hh f hLip a.
    pose V : set X := (fun x : X=>(val x : E)) @^-1` U.
    have hV : open V.
      exact (@open_comp X E (fun x=>val x) U
        (fun x _=>@riemannian_chart_inclusion_continuous R m A g hg x) hU).
    exists V; split; first exact hV; split; first exact hUa.
    move=> T hT hTV.
    pose v := fun x : X=>(val x : E).
    pose Z := v @` T.
    pose G := @riemannian_chart_lift R E n B h hh F hRange.
    have hFLip : is_metric_lipschitz setT F by exists K; split.
    have hZ := @riemannian_reference_coordinate_image_measurable R m A g hg T hT.
    have [b [hCoordinateSource hCoordinateTarget]] :=
      @riemannian_coordinate_area_formula R m n B h hh F hRange hp Z hFLip hZ.
    have hSource : is_measure_subset_integral phi T J b.
      apply: (@riemannian_reference_subset_integral_iff R m A g hg T J
        (@extended_target_riemannian_jacobian R m n B h hh F hRange m) hT _ b).2 hCoordinateSource.
      move=> x hx z.
      exact (@riemannian_map_extended_jacobian_local_coordinates R m n A B g h hg hh f
        U F hRange hU hUA hAgreement x (hTV x hx) m z).
    have hMass : nu T=b.
      rewrite /nu (measure_with_density_laws phi J T) /measure_subset_upper_integral.
      exact: measure_upper_integral_unique (measure_upper_integral_specification phi _) hSource.2.1.
    have hCounts y : @mapping_multiplicity R E Y G Z y=@mapping_multiplicity R X Y f T y.
      have hChart := @mapping_multiplicity_injective_chart R X E Y T v G y
        (fun x z _ _ hEq=>val_inj hEq).
      have hFibre : mapping_fibre (fun x=>G (v x)) T y=mapping_fibre f T y.
        apply/seteqP; split.
        + move=> x [hx hEq]; split; first exact hx.
          have hPoint : G (v x)=f x.
            apply: val_inj; exact: hAgreement x (hTV x hx).
          by rewrite -hPoint.
        + move=> x [hx hEq]; split; first exact hx.
          have hPoint : G (v x)=f x.
            apply: val_inj; exact: hAgreement x (hTV x hx).
          by rewrite hPoint.
      rewrite /mapping_multiplicity hFibre in hChart; exact: esym hChart.
    rewrite hMass.
    apply: (measure_integral_graph_equivalent _ hCoordinateTarget)=> y z.
    change (@mapping_multiplicity R E Y G Z y=z <-> @mapping_multiplicity R X Y f T y=z).
    by rewrite hCounts.
exists (nu S); split; last exact hTarget.
exact (@measurable_density_subset_integral R X phi nu hPhi J S
  (measure_with_density_laws phi J) hJPositive hJMeas hS).
Qed.
