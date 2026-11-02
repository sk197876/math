(** Federer (1969), 3.2.5, pp. 244–245:
    transformation of integrals under each of the three
    alternative conditions. Equality is equality of the
    integral graphs, including undefined signed integrals. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground ExtendedRealOrderTopology PartialFunctionBasic LipschitzUP HausdorffMeasure MappingMultiplicity
  MeasureUP MeasureAlmostUP MeasureAlmostEquality MeasurableFunctionUP MeasureIntegralUP MeasureIntegral
  MeasureIntegralUniqueness MeasureIntegralAlmostEquality AreaTransformIntegrands AreaMeasurableTransform
  AreaSourceMeasurableTransform FiniteMultiplicityWeightRecovery AreaNullWeightChange.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [has_area_transform_alternative]: the three
    alternatives (1), (2), (3) of Federer 3.2.5,
    p. 244: target weight measurability, almost-everywhere
    finite multiplicity, or source weighted-integrand measurability. *)
Definition has_area_transform_alternative (R:realType) m n
    (f:R_n R m->R_n R n) A (g:R_n R n->real_line_metric R):Prop:=
  is_measure_measurable_function (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (partial_function_total g) \/
  measure_almost_everywhere (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    [set y|@mapping_multiplicity R _ _ f A y< +oo] \/
  is_measure_measurable_function (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g).

(** Source for [euclidean_area_integral_transformation]: all
    three alternatives in Federer 3.2.5, pp. 244–245.
    No finite-mass, summability, integral-existence or extra
    measurability hypothesis is imposed. The supporting proof
    works in arbitrary ambient dimensions. *)
Theorem euclidean_area_integral_transformation (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:R_n R n->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  has_area_transform_alternative f A g -> forall a,
  is_measure_integral (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (area_transform_target_integrand f A g) a.
Proof.
move=>hLip hA [hMeas|[hFinite|hSource]] a.
- exact (area_measurable_transform_integral_iff hLip hA hMeas a).
- split=>hI.
  + exact ((area_source_measurable_transform_integral_iff hLip hA hI.1 a).1 hI).
  + have [G [N [hG [hN hAgree]]]]:=finite_multiplicity_measurable_weight_recovery hLip hA hFinite hI.1.
    have [hS hT]:=area_null_target_weight_change hLip hN hAgree.
    have hGT:=measure_integral_almost_equal (@hausdorff_measure_is_measure R _ m)
      hI (measure_almost_equal_sym hT).
    have hGS:=(area_measurable_transform_integral_iff hLip hA hG a).2 hGT.
    exact (measure_integral_almost_equal (euclidean_lebesgue_is_measure R m) hGS hS).
- exact (area_source_measurable_transform_integral_iff hLip hA hSource a).
Qed.

(** Source for [federer_3_2_5]: Federer 3.2.5,
    pp. 244–245, retaining the printed m<=n assumption
    and all three alternative conditions. Both signed
    integrals have exactly the same defined values. *)
Theorem federer_3_2_5 (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:R_n R n->real_line_metric R):
  (m<=n)%N -> is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  has_area_transform_alternative f A g -> forall a,
  is_measure_integral (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) a <->
    is_measure_integral (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (area_transform_target_integrand f A g) a.
Proof. move=>hmn; exact:euclidean_area_integral_transformation. Qed.

(** Source for [area_transform_integrability_iff]: explicit
    definedness consequence of the equation in Federer
    3.2.5, pp. 244–245. Undefined infinity differences
    remain undefined on both sides. *)
Corollary area_transform_integrability_iff (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) A
    (g:R_n R n->real_line_metric R):
  is_metric_lipschitz setT f -> measure_measurable (@euclidean_lebesgue_measure R m) A ->
  has_area_transform_alternative f A g ->
  (is_measure_integrable (@euclidean_lebesgue_measure R m) (area_transform_source_integrand f A g) <->
    is_measure_integrable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
      (area_transform_target_integrand f A g)).
Proof.
move=>hLip hA hAlt; split; move=>[a ha]; exists a.
- exact ((euclidean_area_integral_transformation hLip hA hAlt a).1 ha).
- exact ((euclidean_area_integral_transformation hLip hA hAlt a).2 ha).
Qed.
