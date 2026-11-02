(** Federer (1969), 2.10.12, p. 176: one-dimensional Hausdorff measure of a
    connected set is at least its diameter. Retain the printed distance map
    and interval image argument, using the already proved nonexpanding image
    estimate and H1=L1 on R. Their arbitrary-set forms avoid the printed
    preliminary completion, separability and Borel-hull reductions. they do
    not state this connected-set theorem. No relevant correction occurs in
    the local LaTeX erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normed_module lra.
From Federer Require Import RealMetricBackground NormMetricScaleContinuity MetricDiameterUP MetricDiameter
  HausdorffLengthUP HausdorffLength HausdorffLengthMaps HausdorffLengthReal
  HausdorffLengthCompatibility HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [distance_from_point_nonexpanding]: supporting
    distance-map inequality in the proof of Federer 2.10.12,
    p. 176. It follows directly from the abstract metric
    triangle law and does not assume a normed source. *)
Lemma distance_from_point_nonexpanding (R : realType) (X : metricType R) (a : X) :
  forall x y, (mdist (mdist a x : real_line_metric R) (mdist a y)<=mdist x y)%R.
Proof.
move=> x y; rewrite real_line_metric_distanceE ler_norml.
have h1 := metric_triangle a x y.
have h2 := metric_triangle a y x; rewrite (metric_sym y x) in h2.
apply/andP; split; lra.
Qed.

(** Source for [connected_distance_image_contains_segment]: direct
    interval-image step in the proof of Federer 2.10.12,
    p. 176. The distance image of a connected set containing
    a and b contains [0,distance(a,b)]. The connected-real-set
    interval criterion is general-topology background. *)
Lemma connected_distance_image_contains_segment (R : realType) (X : metricType R)
    (C : set X) (a b : X) : connected C -> C a -> C b ->
  `[0%R,mdist a b] `<=` (fun x => (mdist a x : real_line_metric R)) @` C.
Proof.
move=> hC ha hb.
pose f (x : X) : real_line_metric R := mdist a x.
have hf : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R X [the metricType R of real_line_metric R] f 1 ler01).
  move=> x y; rewrite mul1r; exact: distance_from_point_nonexpanding.
have him : connected (f @` C) := connected_continuous_connected hC (continuous_subspaceT hf).
have hint := (proj1 (connected_intervalP _)) him.
have h0 : (f @` C) 0%R.
  exists a=> //; by rewrite /f mdistxx.
have hr : (f @` C) (mdist a b) by exists b.
move=> t; rewrite /= in_itv /= => ht.
exact: hint 0%R (mdist a b) h0 hr t ht.
Qed.

(** Source for [connected_hausdorff_length_diameter_bound]: direct
    connected-set corollary of Federer 2.10.12, p. 176,
    for the legacy length interface. Empty sets and infinite
    diameter or measure values are included without reductions. *)
Theorem connected_hausdorff_length_diameter_bound (R : realType) (X : metricType R)
    (C : set X) : connected C -> extended_metric_diameter C<=@hausdorff_length R X C.
Proof.
move=> hC; apply: (metric_diameter_least (extended_metric_diameter_specification C)).
- exact: measure_nonnegative (@hausdorff_length_is_measure R X) _.
- move=> a b ha hb.
  have hsub := @connected_distance_image_contains_segment R X C a b hC ha hb.
  have hseg := @measure_mono R [the metricType R of real_line_metric R]
    (@hausdorff_length R [the metricType R of real_line_metric R])
    (@hausdorff_length_is_measure R [the metricType R of real_line_metric R]) _ _ hsub.
  rewrite (hausdorff_length_real_segment (mdist_ge0 a b)) subr0 in hseg.
  apply: le_trans hseg _.
  exact: (@hausdorff_length_nonexpanding R X [the metricType R of real_line_metric R]
    (fun x => (mdist a x : real_line_metric R)) (@distance_from_point_nonexpanding R X a) C).
Qed.

(** Source for [federer_2_10_12]: direct printed conclusion
    of Federer 2.10.12, p. 176, using the current normalized
    integer-degree Hausdorff measure at degree one. No extra
    measurability, finiteness, completeness or separability
    hypothesis is imposed on the connected set or ambient space. *)
Theorem federer_2_10_12 (R : realType) (X : metricType R) (C : set X) :
  connected C -> extended_metric_diameter C<=@hausdorff_measure R X 1 C.
Proof.
move=> hC; rewrite hausdorff_measure_one_length.
exact: connected_hausdorff_length_diameter_bound hC.
Qed.
