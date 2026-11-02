(** Federer (1969), 2.10.45, printed p. 202, first proof paragraph:
    translation in the Euclidean coordinate preserves the product metric.
    The map and inverse are explicit coordinate operations, not new selected
    mathematical objects. Their isometry is derived from the abstract
    squared-distance product hypothesis and the existing Euclidean norm
    laws. Source context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricCartesianProductUP
  SquaredMetricProductUP SquaredMetricProductLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_translation_distance]: supporting
    translation isometry in the first proof
    paragraph of 2.10.45, p. 202,
    from the prescribed Euclidean norm distance. *)
Lemma euclidean_coordinate_translation_distance (R : realType) m
    (a x u : inner_metric_space (@euclidean_inner_productP R m)) :
  mdist (a+x) (a+u)=mdist x u.
Proof.
rewrite !inner_metric_distanceE.
have -> : (a+x)-(a+u)=x-u by rewrite opprD addrACA subrr add0r.
by [].
Qed.

(** Source for [euclidean_product_translation]: direct
    translation in R^m leaving the second
    coordinate fixed, used in 2.10.45,
    p. 202. Its defining expression uses
    only supplied product structure maps. *)
Definition euclidean_product_translation (R : realType) m (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    (first : P -> inner_metric_space (@euclidean_inner_productP R m)) (second : P -> Y)
    (a : inner_metric_space (@euclidean_inner_productP R m)) (p : P) :=
  pair (a+first p) (second p).

(** Source for [euclidean_product_translation_cancel]: supporting
    inverse translation used for the invariance
    assertion in 2.10.45, p. 202. *)
Lemma euclidean_product_translation_cancel (R : realType) m (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) a :
  cancel (euclidean_product_translation pair first second a)
    (euclidean_product_translation pair first second (-a)).
Proof.
move=> p; rewrite /euclidean_product_translation
  (squared_product_first_pair_law hp) (squared_product_second_pair_law hp)
  addrA addNr add0r.
by rewrite (squared_product_recovery_law hp).
Qed.

(** Source for [euclidean_product_translation_isometry]: supporting
    product isometry behind translation invariance
    of gamma in 2.10.45, p. 202.
    The second factor remains an arbitrary metric space. *)
Theorem euclidean_product_translation_isometry (R : realType) m (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) a p q :
  mdist (euclidean_product_translation pair first second a p)
    (euclidean_product_translation pair first second a q)=mdist p q.
Proof.
have he := squared_product_distance_law hp (a+first p) (second p) (a+first q) (second q).
rewrite euclidean_coordinate_translation_distance
  -(squared_metric_product_distance_coordinates hp) in he.
have h1 := mdist_ge0 (euclidean_product_translation pair first second a p)
  (euclidean_product_translation pair first second a q).
have h2 := mdist_ge0 p q.
change (mdist (euclidean_product_translation pair first second a p)
  (euclidean_product_translation pair first second a q)^+2=mdist p q^+2) in he.
nra.
Qed.
