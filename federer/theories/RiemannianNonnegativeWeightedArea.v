(** Federer (1969), 3.2.46, p. 282: extend the
    nonnegative weighted area identity of 3.2.3(2),
    pp. 243–244, to the actual Riemannian metrics.
    Characteristic expansions and countable nonnegative sums
    preserve the actual original map and fibre values. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianMapJacobian
  RiemannianAreaJacobianVolumeMeasurable RiemannianUnweightedArea
  PartialFunctionUP PartialFunctionBasic PartialDensityProduct PartialExtendedOrderLoci
  MeasureUP MeasureDensityUP MeasureDensity MeasureChangeOfDensity
  MeasureSubsetIntegral MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasurableFunctionUP MappingMultiplicity FibreNonnegativeSum WeightedFibreIntegral
  WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion PositiveVanishingWeightsSealed
  WeightedCharacteristicIntegral NonnegativeSum ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_nonnegative_weighted_area]:
    the actual Riemannian nonnegative weighted area formula,
    supporting 3.2.46, p. 282, via 3.2.3(2),
    pp. 243–244. Every actual source-measurable nonnegative
    extended weight is allowed. Fibre sums may be infinite
    or uncountable, integrals may be infinite, and all
    source and target natural dimensions remain. *)
Theorem riemannian_nonnegative_weighted_area (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : (0<=m%:R :> R)%R)
    (u : riemannian_metric_space hg -> extended_real_line R) :
  is_riemannian_path_lipschitz f ->
  is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hp) (partial_function_total u) ->
  (forall x, 0<=u x) ->
  exists a,
    is_measure_integral (riemannian_hausdorff_measure hg m%:R hp)
      (partial_density_product (partial_function_total u) (extended_riemannian_map_jacobian f m)) a /\
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp)
      (partial_function_total (fun y=>(fibre_nonnegative_sum f u y : extended_real_line R))) a.
Proof.
move=> hLip hU hPositive.
pose X := [the choiceType of riemannian_metric_space hg].
pose Y := [the choiceType of riemannian_metric_space hh].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose beta := riemannian_hausdorff_measure hh m%:R hp.
pose J := extended_riemannian_map_jacobian f m.
pose nu := measure_with_density mu J.
have hMu := @riemannian_hausdorff_is_measure R m A g hg m%:R hp.
have hBeta := @riemannian_hausdorff_is_measure R n B h hh m%:R hp.
have hJ := @riemannian_area_jacobian_volume_measurable R m n A B g h hg hh f hp hLip.
have hJPositive := @riemannian_area_jacobian_volume_nonnegative R m n A B g h hg hh f hp hLip.
have hNu := measure_with_density_is_measure hMu hJPositive.
pose r := @PositiveVanishingWeights.value R.
have hWeights := @PositiveVanishingWeights.laws R.
have [E [s [hExpansion _]]] := @measurable_weighted_characteristic_expansion R X mu hMu u r
  hU hPositive hWeights.
have hRepresentation : is_weighted_characteristic_expansion nu u r E s.
  constructor.
  - move=> k; exact (@measure_with_density_measurable R X mu hMu J (E k)
      hJPositive (expansion_sets_measurable hExpansion k)).
  - exact: expansion_characteristic_laws hExpansion.
  - exact: expansion_pointwise_sum hExpansion.
have hCounts k : is_measure_integral beta (partial_function_total
    (fun y=>(@mapping_multiplicity R X Y f (E k) y : extended_real_line R))) (nu (E k)).
  have hE := expansion_sets_measurable hExpansion k.
  have [a [hSource hTarget]] := @riemannian_unweighted_area_formula R m n A B g h hg hh f hp (E k) hLip hE.
  have hMass : nu (E k)=a.
    rewrite /nu (measure_with_density_laws mu J (E k)) /measure_subset_upper_integral.
    exact: measure_upper_integral_unique (measure_upper_integral_specification mu _) hSource.2.1.
  by rewrite hMass.
pose a := nonnegative_sum setT (fun k=>(r k)%:E*nu (E k)).
have hSource : is_measure_integral nu (partial_function_total u) a :=
  weighted_characteristic_expansion_integral hNu (expansion_weights_positive hWeights) hRepresentation.
exists a; split.
- exact: (@measure_density_integral_iff R X mu nu hMu J (partial_function_total u)
    (measure_with_density_laws mu J) hJ hJPositive hU a).1 hSource.
- exact (@weighted_fibre_integral R X Y f nu beta hNu hBeta u r E s
    (expansion_weights_positive hWeights) hRepresentation hCounts).
Qed.
