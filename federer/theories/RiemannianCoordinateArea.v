(** Federer (1969), 3.2.46, p. 282: the
    Riemannian-target area formula with actual multiplicities.
    This supporting coordinate theorem sums the proved
    original Borel pieces and removes the true Jacobian-null
    and image-null remainder. General locally Lipschitz
    charts, source-metric restoration and the signed 3.2.5
    alternatives remain separate from this coordinate case. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions LipschitzUP
  RiemannianTensorUP RiemannianMetricCarrier RiemannianChartLift RiemannianHausdorff
  RiemannianTargetJacobian RiemannianAreaJacobianMeasurable RiemannianAreaNullReduction
  RiemannianAreaBorel RiemannianHausdorffNullEquivalence RealHausdorffMeasure RealPowerNaturalHausdorff
  AreaBorelReductionUP MeasurableAreaBorelReduction AreaNullImageModification
  MeasureUP MeasureFiniteClosure BorelRegularMeasureUP TopologicalBorel
  MeasureDensityUP MeasureDensity DensityCharacteristicIntegral MeasureIntegralUP
  MeasureSubsetIntegral ExtendedRealOrderTopology PartialFunctionBasic MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_coordinate_area_formula]: the
    target-metric area identity supporting 3.2.46, p. 282,
    on every Lebesgue-measurable coordinate source subset,
    with actual counting multiplicity and actual partial
    Jacobian. No injectivity, rank or finiteness premise;
    all dimensions including zero are retained. This
    supporting case assumes the coordinate representative
    globally Euclidean Lipschitz; it does not claim the
    complete Riemannian 3.2.5 extension by itself. *)
Theorem riemannian_coordinate_area_formula (R : realType) m n A h
    (hh : @is_continuous_riemannian_tensor R n A h)
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (hf : forall x, A (f x)) (hp : 0<=m%:R :> R) (S : set (R_n R m)) :
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) S ->
  exists a,
    is_measure_subset_integral (@euclidean_lebesgue_measure R m) S
      (@extended_target_riemannian_jacobian R m n A h hh f hf m) a /\
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp)
      (partial_function_total (fun y=>(@mapping_multiplicity R _ _
        (@riemannian_chart_lift R _ n A h hh f hf) S y : extended_real_line R))) a.
Proof.
move=> hLip hS.
pose X := [the choiceType of inner_metric_space (@euclidean_inner_productP R m)].
pose M := [the choiceType of riemannian_metric_space hh].
pose F := @riemannian_chart_lift R X n A h hh f hf.
pose phi := @euclidean_lebesgue_measure R m.
pose J := @extended_target_riemannian_jacobian R m n A h hh f hf m.
pose nu := measure_with_density phi J.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
have hPhi := euclidean_lebesgue_is_measure R m.
have hJPositive := @target_riemannian_jacobian_nonnegative_almost R m n A h hh f hf m hLip.
have hNu := measure_with_density_is_measure hPhi hJPositive.
have hBeta := @riemannian_hausdorff_is_measure R n A h hh m%:R hp.
have [C [hC [hCS [hLocus [hEuclideanNull hEuclideanImageNull]]]]] := measurable_injective_area_subset hLip hS.
have hCMeas := @borel_regular_borel_measurable R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
  phi hPhi (euclidean_lebesgue_borel_regular R m) C hC.
have hDifferenceMeas := measure_measurable_difference hPhi hS hCMeas.
have hRNull := @riemannian_area_null_reduction R m n A h hh f hf (S `\` C)
  hLip hDifferenceMeas hEuclideanNull.
have hImage : beta (F @` (S `\` C))=0%E.
  apply: (@riemannian_hausdorff_null_iff R n A h hh m%:R hp (F @` (S `\` C))).2.
  have hCoordinates : (fun z : riemannian_metric_space hh=>val z) @` (F @` (S `\` C))=
      f @` (S `\` C).
    apply/seteqP; split=> y.
    - move=> [z [x hx <-] <-]; by exists x.
    - move=> [x hx <-]; exists (F x); first by exists x.
      by [].
  by rewrite hCoordinates real_hausdorff_measure_natural.
have hCFormula := @riemannian_area_injective_borel R m n A h hh f hf hp C hLip hC hLocus.
have hWhole := @area_formula_null_image_modification R X M F nu beta hNu hBeta C S
  hCS hRNull hImage hCFormula.
exists (nu S); split; last exact hWhole.
exact (@measurable_density_subset_integral R X phi nu hPhi J S
  (measure_with_density_laws phi J) hJPositive
  (@extended_target_riemannian_area_jacobian_measurable R m n A h hh f hf hLip) hS).
Qed.
