(** Federer (1969), 2.3.2(8), p. 74: reduction to the numerical criterion by
    distance to a nonempty closed set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition
  ExtendedRealOrderTopology MeasurableSeparationUP MetricSetDistanceUP MetricSetDistanceBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_distance_levels_separated]: supporting
    separation of the distance levels used in Federer 2.3.2(8),
    p. 74. Their cross distances are bounded below by b-a. *)
Lemma metric_distance_levels_separated (R : realType) (Y : metricType R)
    (C : set Y) (d : Y -> R) (hd : is_metric_set_distance C d) (a b : R) :
  (a < b)%R -> metric_sets_positively_separated
    [set y | (d y)%:E <= a%:E] [set y | b%:E <= (d y)%:E].
Proof.
move=> hab; exists (b-a)%R; split; first by rewrite subr_gt0.
move=> x hx y hy.
have hx' : (d x <= a)%R by move: hx; rewrite /= lee_fin.
have hy' : (b <= d y)%R by move: hy; rewrite /= lee_fin.
apply: le_trans (lerB hy' hx') _.
rewrite metric_sym; exact: metric_set_distance_subtract_bound hd y x.
Qed.

(** Source for [image_separation_distance_level_separated]: direct
    application of the hypothesis in Federer 2.3.2(8), p. 74,
    to the two distance levels. This does not presume measurability
    or continuity of the original function. *)
Lemma image_separation_distance_level_separated (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (f : partial_function X Y)
    (C : set Y) (d : Y -> R) (hd : is_metric_set_distance C d) :
  is_measure_image_separated mu f ->
  is_measure_level_separated mu
    (partial_function_postcompose f (fun y => ((d y)%:E : extended_real_line R))).
Proof.
move=> hs T a b hab.
rewrite !partial_function_postcompose_preimage.
apply: hs; exact (@metric_distance_levels_separated R Y C d hd a b hab).
Qed.
