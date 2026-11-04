(** Federer (1969), 3.2.46, p. 282: the full
    area transformation 3.2.5, pp. 244–245, with
    actual source and target Riemannian metrics. All
    three printed alternatives are retained and discharged
    through proved local reductions. The coarea assertion
    of 3.2.46 remains a separate theorem obligation. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff RiemannianPathLipschitz
  RiemannianAreaTransformIntegrands RiemannianAreaMeasurableTransform
  RiemannianAreaSourceMeasurableTransform RiemannianFiniteMultiplicityWeightRecovery RiemannianAreaNullWeightChange
  PartialFunctionBasic MappingMultiplicity MeasureUP MeasureAlmostUP MeasureAlmostEquality
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [has_riemannian_area_transform_alternative]:
    the same three alternatives (1), (2), (3) of
    3.2.5, p. 244: target weight measurability, almost
    everywhere finite actual multiplicity, or measurability
    of the displayed source weighted-Jacobian integrand,
    with the actual metrics required by 3.2.46, p. 282. *)
Definition has_riemannian_area_transform_alternative (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) : Prop :=
  is_measure_measurable_function (riemannian_hausdorff_measure hh m%:R hp) (partial_function_total u) \/
  measure_almost_everywhere (riemannian_hausdorff_measure hh m%:R hp)
    [set y | (@mapping_multiplicity R _ _ f S y< +oo)%E] \/
  is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hp)
    (riemannian_area_source_integrand f S u).

(** Source for [riemannian_area_integral_transformation]:
    full signed 3.2.5, pp. 244–245, for the actual
    Riemannian objects of 3.2.46, p. 282. Only
    original path-distance Lipschitz continuity, original
    completed source measurability and one of the printed
    alternatives are assumed. Every defined value, including
    signed infinity, is preserved; undefined infinity
    differences remain undefined on both sides. *)
Theorem riemannian_area_integral_transformation (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  has_riemannian_area_transform_alternative f hp S u -> forall a,
  is_measure_integral (riemannian_hausdorff_measure hg m%:R hp) (riemannian_area_source_integrand f S u) a <->
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp) (riemannian_area_target_integrand f S u) a.
Proof.
move=> hLip hS [hMeas|[hFinite|hSource]] a.
- exact: (@riemannian_area_measurable_transform_integral_iff R m n A B g h hg hh f hp S u hLip hS hMeas a).
- split=> hi.
  + exact: (@riemannian_area_source_measurable_transform_integral_iff R m n A B g h hg hh f hp S u
      hLip hS hi.1 a).1 hi.
  + have [U [N [hU [hN hAgree]]]] := @riemannian_finite_multiplicity_weight_recovery R m n A B g h hg hh f
      hp S u hLip hS hFinite hi.1.
    have [hSourceAgreement hTargetAgreement] := @riemannian_area_null_target_weight_change R m n A B g h hg hh f
      hp S u U N hLip hN hAgree.
    have hUTarget := @measure_integral_almost_equal R [the choiceType of riemannian_metric_space hh]
      (riemannian_hausdorff_measure hh m%:R hp) (@riemannian_hausdorff_is_measure R n B h hh m%:R hp)
      _ _ a hi (measure_almost_equal_sym hTargetAgreement).
    have hUSource := (@riemannian_area_measurable_transform_integral_iff R m n A B g h hg hh f
      hp S U hLip hS hU a).2 hUTarget.
    exact (@measure_integral_almost_equal R [the choiceType of riemannian_metric_space hg]
      (riemannian_hausdorff_measure hg m%:R hp) (@riemannian_hausdorff_is_measure R m A g hg m%:R hp)
      _ _ a hUSource hSourceAgreement).
- exact: (@riemannian_area_source_measurable_transform_integral_iff R m n A B g h hg hh f hp S u hLip hS hSource a).
Qed.

(** Source for [federer_3_2_46_area]: the area part
    of 3.2.46, p. 282, retaining the printed m<=n
    hypothesis from 3.2.5, p. 244, all three
    alternatives, original Riemannian metrics and original
    partial Jacobian. All natural dimensions, singular
    maps and infinite integrals remain. *)
Theorem federer_3_2_46_area (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg))
    (u : riemannian_metric_space hh -> real_line_metric R) :
  (m<=n)%N -> is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  has_riemannian_area_transform_alternative f hp S u -> forall a,
  is_measure_integral (riemannian_hausdorff_measure hg m%:R hp) (riemannian_area_source_integrand f S u) a <->
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp) (riemannian_area_target_integrand f S u) a.
Proof.
move=> hDimension.
exact: (@riemannian_area_integral_transformation R m n A B g h hg hh f hp S u).
Qed.
