(** Federer (1969), 3.2.3(1), pp. 243–244:
    the area formula for every Lebesgue-measurable source
    set, with the actual Jacobian and counting multiplicity.
    Both integrals are proved to exist, including infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral PartialFunctionBasic ExtendedRealOrderTopology
  EuclideanJacobianMeasurable JacobianDensityMeasure HausdorffMeasure MappingMultiplicity
  LipschitzUP AreaBorelReductionUP MeasurableAreaBorelReduction AreaInjectiveBorel AreaNullImageModification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_area_formula]: all measurable
    sets in Federer 3.2.3(1), pp. 243–244.
    The proof actually works in every pair of ambient
    dimensions; the numbered wrapper retains m<=n exactly
    as printed. No decomposition or measurability of the
    image or multiplicity is an extra hypothesis. *)
Theorem euclidean_area_formula (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R m) A
      (extended_euclidean_jacobian f) a /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_function_total (fun y=>(@mapping_multiplicity R _ _ f A y:extended_real_line R))) a.
Proof.
move=>hLip hA.
have [C [hC [hCA [hCLocus [hNu hImage]]]]]:=measurable_injective_area_subset hLip hA.
have hCFormula:=area_formula_injective_borel hLip hC hCLocus.
have hAFormula:=area_formula_null_image_modification
  (euclidean_jacobian_measure_is_measure hLip) (@hausdorff_measure_is_measure R _ m)
  hCA hNu hImage hCFormula.
exists (euclidean_jacobian_measure f A); split; last exact hAFormula.
exact (euclidean_jacobian_measure_integral hLip hA).
Qed.

(** Source for [federer_3_2_3_1]: Federer 3.2.3(1),
    pp. 243–244, with the printed m<=n hypothesis,
    arbitrary measurable A, infinite integrals and zero
    dimensions included. *)
Theorem federer_3_2_3_1 (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A:
  (m<=n)%N -> is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  exists a,is_measure_subset_integral (@euclidean_lebesgue_measure R m) A
      (extended_euclidean_jacobian f) a /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (partial_function_total (fun y=>(@mapping_multiplicity R _ _ f A y:extended_real_line R))) a.
Proof. move=>hmn; exact:euclidean_area_formula. Qed.
