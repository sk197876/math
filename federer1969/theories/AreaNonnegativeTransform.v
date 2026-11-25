(** Federer (1969), 3.2.5(1), pp. 244–245:
    the nonnegative integral transformation by the characteristic
    approximation argument of 3.2.3, with completed target
    measurability and all infinite integral values allowed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralAlmostEquality
  MeasureChangeOfDensity MeasurableFunctionUP LipschitzUP HausdorffMeasure EuclideanJacobianMeasurable
  JacobianDensityMeasure MappingMultiplicity AreaTransformIntegrands AreaRankWeightUP AreaRankWeightExistence
  AreaRankWeightAgreement AreaNonnegativeWeighted PositiveJacobianImageNull BorelAreaSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [area_nonnegative_transform]: the nonnegative
    extension of the characteristic-function identity in Federer
    3.2.5(1), p. 245. No source integrability or
    boundedness of the target weight is required. *)
Theorem area_nonnegative_transform (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:inner_metric_space (@euclidean_inner_productP R n)->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  is_measure_measurable_function (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_total g) -> (forall y,(0<=g y)%R) ->
  exists a,is_measure_integral (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) a /\
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (area_transform_target_integrand f A g) a.
Proof.
move=>hLip hA hg hg0.
pose mu:=@euclidean_lebesgue_measure R m.
pose beta:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hm:=euclidean_lebesgue_is_measure R m.
have hb:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have [u [hU hUMeas]]:=measurable_area_rank_weight_exists hLip hA hg.
have [a [hSource hTarget]]:=area_nonnegative_weighted_integral hLip hUMeas (area_rank_weight_nonnegative hU hg0).
have hDensity:=(@measure_density_integral_iff R _ mu (euclidean_jacobian_measure f) hm
  (extended_euclidean_jacobian f) (partial_function_total u) (euclidean_jacobian_measure_laws f)
  (extended_euclidean_jacobian_measurable hLip) (euclidean_jacobian_nonnegative_almost hLip) hUMeas a).1 hSource.
exists a; split.
- exact (measure_integral_almost_equal hm hDensity (area_rank_weight_source_agreement hLip hU)).
- apply:(measure_integral_almost_equal hb hTarget).
  have hNull:=nonpositive_jacobian_image_null hLip.
  have hOff:measure_almost_everywhere beta (~` (f @` (~` positive_euclidean_jacobian_locus f))).
    by rewrite /measure_almost_everywhere setCK.
  apply:(@measure_almost_everywhere_mono R _ beta hb _ _ _ hOff)=>y hy.
  exists ((g y)%:E*@mapping_multiplicity R _ _ f A y); split; last by [].
  exact (area_rank_weight_fibre_sum hU hg0 hy).
Qed.
