(** Federer (1969), 3.2.46, p. 282: the actual
    area Jacobian is measurable for actual Riemannian source
    volume, not merely ordinary coordinates. Proved completed
    top-volume and null-set equivalences justify the transfer. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RiemannianChartReference
  RiemannianVolumeCompletion RiemannianMapJacobian RiemannianMapAreaJacobianMeasurable
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_area_jacobian_volume_measurable]:
    measurability of the original partial Jacobian for
    actual H_rho^m source volume, supporting 3.2.46,
    p. 282. It follows from original path-Lipschitz
    continuity; no separate derivative or measurability
    premise is supplied. *)
Theorem riemannian_area_jacobian_volume_measurable (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) :
  is_riemannian_path_lipschitz f ->
  is_measure_measurable_function (riemannian_hausdorff_measure hg m%:R hp)
    (extended_riemannian_map_jacobian f m).
Proof.
move=> hLip.
have hJ := @extended_riemannian_map_area_jacobian_measurable R m n A B g h hg hh f hLip.
constructor.
- apply: (@riemannian_volume_reference_null_iff R m A g hg hp _).2.
  exact: measurable_function_domain hJ.
- move=> U hU.
  exact: (@riemannian_volume_reference_measurable_iff R m A g hg hp _).2
    (measurable_function_open_preimage hJ hU).
Qed.

(** Source for [riemannian_area_jacobian_volume_nonnegative]:
    almost-everywhere nonnegativity of the actual original
    area Jacobian for actual source volume, supporting
    3.2.46, p. 282. Its conull domain is derived
    rather than assumed, and all natural dimensions remain. *)
Theorem riemannian_area_jacobian_volume_nonnegative (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hp : 0<=m%:R :> R) :
  is_riemannian_path_lipschitz f ->
  measure_almost_everywhere (riemannian_hausdorff_measure hg m%:R hp)
    (partial_extended_nonnegative_locus (extended_riemannian_map_jacobian f m)).
Proof.
move=> hLip.
have hJ := @riemannian_area_jacobian_volume_measurable R m n A B g h hg hh f hp hLip.
apply: (@measure_almost_everywhere_mono R _ _
  (@riemannian_hausdorff_is_measure R m A g hg m%:R hp) _ _ _
  (measurable_function_domain hJ))=> x [j [r [hr hRj]]].
exists r%:E; split; first by exists r; split.
rewrite lee_fin; exact: riemannian_map_jacobian_nonnegative hr.
Qed.
