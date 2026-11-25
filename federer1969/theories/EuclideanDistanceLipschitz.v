(** Federer (1969), 3.2.34, p. 271: the actual
    distance to the original closed set is globally
    Lipschitz with bound one. The scalar target is
    identified isometrically with the Euclidean line. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  EuclideanOneCoordinate EuclideanOneNormDifferential RealNormUP NormMetric MetricSetDistanceUP
  MetricSetDistanceBasic LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distance_norm_laws]: supporting
    the nearest-segment calculation in Federer 3.2.34,
    p. 271. The independent metric-distance laws transfer
    unchanged to the canonical metric induced by its
    existing Euclidean norm. *)
Lemma euclidean_distance_norm_laws (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d:
  is_metric_set_distance S d ->
  @is_metric_set_distance R [the metricType R of real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))] S d.
Proof.
move=>hD; constructor.
- move=>x s hs; exact:(@metric_set_distance_lower R
    (inner_metric_space (@euclidean_inner_productP R n)) S d hD x s hs).
- move=>x r hb; exact:(@metric_set_distance_greatest R
    (inner_metric_space (@euclidean_inner_productP R n)) S d hD x r hb).
Qed.

(** Source for [euclidean_distance_norm_lipschitz]:
    Lip(f)<=1 in Federer 3.2.34, p. 271,
    in the pairwise norm form used to bound
    every actual differential. No closedness or boundedness
    premise is needed for this consequence of the laws. *)
Lemma euclidean_distance_norm_lipschitz (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d:
  is_metric_set_distance S d ->forall x y,
  inner_norm (@euclidean_inner_productP R 1)
    (euclidean_one_embed (d x)-euclidean_one_embed (d y))<=
    inner_norm (@euclidean_inner_productP R n) (x-y).
Proof.
move=>hd x y.
rewrite euclidean_one_norm_coordinate /euclidean_one_embed !ffunE.
exact:(metric_set_distance_lipschitz_one hd x y).
Qed.

(** Source for [euclidean_distance_lipschitz]: the global
    Lipschitz premise for the application of 3.2.11 in
    Federer 3.2.34, p. 271, using the actual
    distance and the original Euclidean source. *)
Lemma euclidean_distance_lipschitz (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d:
  is_metric_set_distance S d ->is_metric_lipschitz setT
    (fun x:inner_metric_space (@euclidean_inner_productP R n)=>euclidean_one_embed (d x)).
Proof.
move=>hd; exists 1; split; first exact:ltr01.
split; first by [].
move=>x y _ _; rewrite !inner_metric_distanceE mul1r.
exact:(euclidean_distance_norm_lipschitz hd x y).
Qed.
