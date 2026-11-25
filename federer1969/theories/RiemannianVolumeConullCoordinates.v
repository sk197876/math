(** Federer (1969), 3.2.46, pp. 281–282:
    a coordinate conull set remains conull for actual
    Riemannian volume. The actual volume and reference
    null-set equivalence proves this even for arbitrary
    nonmeasurable exceptional coordinate sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianChartReference RiemannianVolumeCompletion
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_volume_conull_coordinate_preimage]:
    actual local coordinates transport conull conclusions,
    supporting 3.2.46, p. 282. The ordinary
    coordinate exceptional set is genuinely null; no
    blanket completed-preimage measurability claim is used. *)
Theorem riemannian_volume_conull_coordinate_preimage (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (hp : 0<=n%:R :> R) (P : set (R_n R n)) :
  measure_almost_everywhere (@euclidean_lebesgue_measure R n) P ->
  measure_almost_everywhere (riemannian_hausdorff_measure hg n%:R hp)
    [set y : riemannian_metric_space hg | P (val y)].
Proof.
move=> hP.
apply:(@riemannian_volume_reference_null_iff R n A g hg hp _).2.
rewrite riemannian_chart_reference_value.
apply:(@measure_null_subset R _ (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) _ (~` P) _ hP).
by move=> z [y hy <-].
Qed.
