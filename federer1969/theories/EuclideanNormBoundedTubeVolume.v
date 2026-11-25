(** Federer (1969), 3.2.36, p. 272:
    uniformly norm-bounded sources have a common
    finite containing ball for their unit tubes. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  MetricSetDistanceUP MetricDistanceTube MetricOpenThickening MetricClosedBalls
  EuclideanLebesgueDimensions MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_norm_bounded_tube_volume]:
    supporting the common geometric error bound
    in the continuity deduction of Federer
    3.2.36, p. 272. The actual unit
    tube is contained in the closed norm
    ball of radius c+1 when the original
    source has norm at most c. This
    follows from distance approximation and the
    metric triangle law; no source measurability,
    convexity or chosen nearest-point field is
    needed for this supporting inequality. *)
Lemma euclidean_norm_bounded_tube_volume (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (c:R):
  is_metric_set_distance S d ->
  (forall x,S x ->(inner_norm (@euclidean_inner_productP R n) x<=c)%R) ->
  euclidean_lebesgue_measure n [set x|(d x<1)%R]<=
    euclidean_lebesgue_measure n (@metric_closed_ball R
      (inner_metric_space (@euclidean_inner_productP R n)) 0%R (c+1)%R).
Proof.
move=>hD hS.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
rewrite (@metric_distance_tube_thickening R X S d 1%R hD).
apply:(measure_mono (euclidean_lebesgue_is_measure R n))=>x [y hy hyx].
change (is_true (mdist (0%R:X) x<=c+1)%R).
apply:le_trans (metric_triangle (0%R:X) y x) _.
have hNorm:mdist (0%R:X) y=inner_norm (@euclidean_inner_productP R n) y.
  by rewrite inner_metric_distanceE sub0r inner_normN.
rewrite hNorm; apply:lerD; first exact:hS y hy.
exact:ltW hyx.
Qed.
