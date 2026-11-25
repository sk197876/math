(** Federer (1969), 3.2.46, p. 282: actual
    Riemannian-volume measurable sets have genuine increasing
    compact cores up to a null remainder. Completed
    reference-volume agreement and the compact reduction of
    2.10.26, p. 190, prove the original-set assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions CoareaNullFibres CountablyMeasurableUP CountablyMeasurableSubsets
  ProperMetricSigmaFiniteCompactCore RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianChartReference RiemannianReferenceSetImage
  RiemannianVolumeCompletion RiemannianCompactCoordinates
  MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_volume_compact_core]:
    the compact approximation needed for the actual
    coarea extension in 3.2.46, p. 282.
    The original source need not be Borel or finite;
    every compact lies in that original source and
    the actual discarded Riemannian volume is zero.
    Empty and disconnected charts require no exception. *)
Theorem riemannian_volume_compact_core (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hp : 0<=m%:R :> R) (S : set (riemannian_metric_space hg)) :
  measure_measurable (riemannian_hausdorff_measure hg m%:R hp) S ->
  exists K : nat -> set (riemannian_metric_space hg), (forall n, compact (K n)) /\
    (forall n, K n `<=` S) /\ (forall n j, (n<=j)%N -> K n `<=` K j) /\
    riemannian_hausdorff_measure hg m%:R hp (S `\` (\bigcup_n K n))=0%E.
Proof.
move=> hS.
pose X := [the metricType R of riemannian_metric_space hg].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose T := (fun x : X=>(val x : E)) @` S.
have hReference := (@riemannian_volume_reference_measurable_iff R m A g hg hp S).1 hS.
have hT := @riemannian_reference_coordinate_image_measurable R m A g hg S hReference.
have hCount := @measurable_subset_countably_measurable R E (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) T setT hT (fun x _=>Logic.I)
  (euclidean_lebesgue_countably_measurable R m).
have [C [hCCompact [hCSubset [hCIncreasing hNull]]]] :=
  @proper_metric_sigma_finite_compact_core R E (@euclidean_lebesgue_measure R m) 0 T
    (euclidean_lebesgue_is_measure R m) (euclidean_lebesgue_borel_regular R m)
    (@coarea_euclidean_source_proper R m) hCount.
pose K n : set X := [set x | C n (val x)].
have hKCompact n : compact (K n).
  apply:riemannian_compact_coordinate_preimage (hCCompact n) _.
  move=> z hz; have [x hx <-] := hCSubset n z hz; exact:set_valP x.
have hKSubset n : K n `<=` S.
  move=> x hx; have [z hz hValue] := hCSubset n (val x) hx.
  have hzx : z=x := val_inj hValue; by rewrite -hzx.
have hKIncreasing n j (hnj : (n<=j)%N) : K n `<=` K j.
  move=> x hx; exact:hCIncreasing n j hnj (val x) hx.
exists K; split; first exact hKCompact; split; first exact hKSubset.
split; first exact hKIncreasing.
apply:(@riemannian_volume_reference_null_iff R m A g hg hp _).2.
rewrite riemannian_chart_reference_value.
apply:(@measure_null_subset R E (@euclidean_lebesgue_measure R m)
  (euclidean_lebesgue_is_measure R m) _ (T `\` (\bigcup_n C n)) _ hNull).
move=> z [x [hx hOutside] <-]; split; first by exists x.
move=> [n _ hxC]; apply:hOutside; by exists n.
Qed.
