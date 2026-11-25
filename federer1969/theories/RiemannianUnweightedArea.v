(** Federer (1969), 3.2.46, p. 282: area with
    actual source and target Riemannian metrics. The
    original map, source subset, differential, Jacobian and
    counting multiplicities are retained. This file proves
    the unweighted identity; it does not claim the signed
    alternatives of 3.2.5 or the coarea extension complete. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianChartReference
  RiemannianVolumeCompletion RiemannianMapJacobian RiemannianMapReferenceArea
  RiemannianSubsetSourceIntegral MappingMultiplicity PartialFunctionBasic
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_unweighted_area_formula]: the
    characteristic-weight area consequence of 3.2.46, p. 282,
    extending 3.2.3, pp. 243–244. Original path-distance
    Lipschitz continuity and original completed-measurable S
    suffice. No global coordinate bound, derivative field,
    rank, finite-mass or finite-fibre premise is imposed.
    All natural dimensions, including zero, are retained. *)
Theorem riemannian_unweighted_area_formula (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg)) :
  is_riemannian_path_lipschitz f ->
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  exists a,
    is_measure_subset_integral (riemannian_hausdorff_measure hg m%:R hp) S
      (extended_riemannian_map_jacobian f m) a /\
    is_measure_integral (riemannian_hausdorff_measure hh m%:R hp)
      (partial_function_total (fun y=>(@mapping_multiplicity R _ _ f S y : extended_real_line R))) a.
Proof.
move=> hLip hS.
have hReference := (@riemannian_volume_reference_measurable_iff R m A g hg hp S).1 hS.
have [a [hSource hTarget]] :=
  @riemannian_map_reference_area_formula R m n A B g h hg hh f hp S hLip hReference.
exists a; split; last exact hTarget.
exact: (@riemannian_subset_area_source_integral_iff R m n A B g h hg hh f hp S hLip hReference a).2 hSource.
Qed.
