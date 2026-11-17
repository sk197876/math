(** Original bounded convex vertical tubes for the Fubini
    calculation in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  CoveringFamilyUP EuclideanLinearMaps ScalarConvexLength VectorSetSum VectorSetSumLaws EuclideanPrefixBallSums
  EuclideanPrefixCompression EuclideanBallVectorSumTube EuclideanNormSetDistance EuclideanDistanceTubeConvex
  EuclideanDistanceTubeBasic MetricSetDistanceSealed MetricOpenThickening MetricOpenThickeningClosure
  MetricBoundedClosureLaws BoundedConvexLebesgueMeasurable EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_convex_vertical_open_tube_geometry]: supporting
    original nonclosed-source Fubini in Federer 3.2.45,
    p. 279. The original vertical open ball is
    a linear image of the ambient open ball and
    has convex image. Its sum with the original
    bounded convex C is convex and lies in the
    already proved bounded ambient distance tube.
    Bounded-convex measurability and compact closure
    finiteness give the remaining Fubini hypotheses.
    No compactness or Borel premise on C is added. *)
Theorem bounded_convex_vertical_open_tube_geometry (R : realType) n m
    (C : set (inner_metric_space (@euclidean_inner_productP R n))) (r : R) :
  C !=set0 -> is_inner_convex C -> metric_set_bounded C -> 0<r ->
  let T := vector_set_sum C
    ((@euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1)) @`
      [set x | inner_norm (@euclidean_inner_productP R n) x<r]) in
  is_inner_convex T /\ metric_set_bounded T /\
    measure_measurable (@euclidean_lebesgue_measure R n) T /\
    (@euclidean_lebesgue_measure R n T< +oo)%E.
Proof.
move=> hNonempty hConvex hBound hr T.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose D := @euclidean_diagonal_map R n (fun j => if (j<m)%N then 0 else 1).
pose B : set X := [set x | inner_norm (@euclidean_inner_productP R n) x<r].
have hZeroConvex : @is_inner_convex R (R_n R n) [set 0].
  move=> x y -> -> t _ _; by rewrite !scaler0 add0r.
have hBallConvex : is_inner_convex B.
  exact: (@euclidean_distance_tube_convex R n [set 0]
    (inner_norm (@euclidean_inner_productP R n)) r (euclidean_norm_set_distance R n) hZeroConvex).
have hTConvex : is_inner_convex T.
  exact: vector_set_sum_inner_convex hConvex (linear_image_inner_convex hBallConvex).
have hBallImage : D @` B `<=` B.
  move=> x [y hy <-].
  change (is_true (inner_norm (@euclidean_inner_productP R n) (D y)<r)).
  exact: le_lt_trans (@euclidean_prefix_zero_norm_bound R n m y) hy.
have hIntoTube : T `<=` metric_open_thickening C r.
  rewrite euclidean_ball_vector_sum_tube.
  have hSum : vector_set_sum C (D @` B) `<=` vector_set_sum C B :=
    vector_set_sum_monotone (@subset_refl X C) hBallImage.
  exact hSum.
pose d := @MetricSetDistance.value R [the metricType R of X] C hNonempty.
have hDistance := @MetricSetDistance.laws R [the metricType R of X] C hNonempty.
have hAmbientBound : metric_set_bounded (metric_open_thickening C r).
  rewrite (@metric_open_thickening_distance R X C d r hDistance).
  exact: (@euclidean_distance_tube_bounded R n C d r hNonempty hDistance hBound hr).
have hTBound : metric_set_bounded T := metric_bounded_subset hIntoTube hAmbientBound.
have hMeasurable := bounded_convex_lebesgue_measurable hTConvex hTBound.
have hFinite : (@euclidean_lebesgue_measure R n T< +oo)%E.
  apply: le_lt_trans (measure_mono (euclidean_lebesgue_is_measure R n) (@subset_closure X T)) _.
  exact: euclidean_compact_finite (euclidean_bounded_closure_compact hTBound).
by split=> //; split=> //; split.
Qed.
