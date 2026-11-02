(** Federer (1969), 3.2.35, p. 272:
    actual orthogonal projection preserves boundedness
    of the original convex body and its tubes. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace EuclideanProjectionMetric MetricDiameterUP MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_projection_bounded_image]: supporting
    the original projected-body hypotheses in
    Federer 3.2.35, p. 272. The actual
    contraction inequality bounds the target diameter
    by the original sealed diameter. Only its
    finite upper bound is used; no measurability,
    closedness or new radius witness is assumed. *)
Lemma euclidean_projection_bounded_image (R:realType) n m
    (p:orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  metric_set_bounded S ->@metric_set_bounded R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    (euclidean_projection_linear p @` S).
Proof.
move=>hBound.
pose X:=[the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose Y:=[the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose D:=@extended_metric_diameter R X S.
have hD:=@extended_metric_diameter_specification R X S.
apply:(le_lt_trans _ hBound).
apply:(@metric_diameter_least R Y (euclidean_projection_linear p @` S) _
  (@extended_metric_diameter_specification R Y (euclidean_projection_linear p @` S)) D
  (metric_diameter_nonnegative hD)).
move=>u v [x hx <-] [y hy <-].
apply:(le_trans _ (@metric_diameter_upper R X S D hD x y hx hy)).
rewrite lee_fin; exact:(euclidean_projection_nonexpanding p x y).
Qed.
