(** Federer (1969), 3.2.10, p. 248: the final
    application of the area formula to the injective fibre
    parametrisation. This supporting consequence of 3.2.3,
    pp. 243–244, retains arbitrary measurable source sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions HausdorffMeasure LipschitzUP MeasureUP
  PartialFunctionUP PartialFunctionBasic EuclideanJacobianMeasurable EuclideanAreaFormula
  MeasureIntegralUP MeasureIntegralUniqueness MeasureSubsetIntegral
  LipschitzMeasurableImages PartitionMultiplicityIntegral MeasureAlmostUP
  MeasureIntegralAlmostEquality MeasureDensityTransfer ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_injective_area_mass]: the final
    equality in Federer 3.2.10, p. 248, applying
    3.2.3(1), pp. 243–244, to an injective slice
    restriction. Measurability of the image is proved from
    Lipschitzness and source measurability, and infinite mass is allowed. *)
Theorem euclidean_injective_area_mass (R:realType) k m
    (f:inner_metric_space (@euclidean_inner_productP R k)->
      inner_metric_space (@euclidean_inner_productP R m)) (C:set (R_n R k)):
  is_metric_lipschitz setT f ->measure_measurable (@euclidean_lebesgue_measure R k) C ->
  {in C &,injective f} ->
  is_measure_subset_integral (@euclidean_lebesgue_measure R k) C
    (extended_euclidean_jacobian f)
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k (f @` C)).
Proof.
move=>hf hC hInj.
have [a [hSource hTarget]]:=euclidean_area_formula hf hC.
have hImage:=euclidean_lipschitz_measurable_image hf hC.
have hMass:=injective_multiplicity_integral (@hausdorff_measure_is_measure R _ k) hInj hImage.
have he:=measure_integral_unique hTarget hMass.
by rewrite he in hSource.
Qed.

(** Source for [euclidean_injective_area_mass_representative]:
    the same last equality in Federer 3.2.10, p. 248,
    for any integrand almost equal to the actual slice Jacobian.
    The source cutoff retains its exact subset-integral convention. *)
Lemma euclidean_injective_area_mass_representative (R:realType) k m
    (f:inner_metric_space (@euclidean_inner_productP R k)->
      inner_metric_space (@euclidean_inner_productP R m)) (C:set (R_n R k))
    (g:partial_function (R_n R k) (extended_real_line R)):
  is_metric_lipschitz setT f ->measure_measurable (@euclidean_lebesgue_measure R k) C ->
  {in C &,injective f} ->
  measure_almost_equal (@euclidean_lebesgue_measure R k) (extended_euclidean_jacobian f) g ->
  is_measure_subset_integral (@euclidean_lebesgue_measure R k) C g
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k (f @` C)).
Proof.
move=>hf hC hInj hEqual.
have hI:=euclidean_injective_area_mass hf hC hInj.
exact (measure_integral_almost_equal (euclidean_lebesgue_is_measure R k) hI
  (zero_extension_almost_equal (euclidean_lebesgue_is_measure R k) 0 C hEqual)).
Qed.
