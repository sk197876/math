(** Federer (1969), 2.2.10, p. 66: supporting properties of the distance to
    the complement of an open set. All consequences here use only the
    greatest-lower-bound specification, not its witness. Source context and
    nonempty-set convention: MetricSetDistanceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_set_distance_nonnegative]: supporting
    nonnegativity of dist(x,X minus S) in Federer 2.2.10,
    p. 66, obtained because zero bounds all point distances below. *)
Lemma metric_set_distance_nonnegative (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) x : 0 <= d x.
Proof.
apply: (@metric_set_distance_greatest R T A d hd x 0)=> a _.
exact: mdist_ge0.
Qed.

(** Source for [metric_set_distance_unique]: supporting uniqueness
    of the abstract infimum in Federer 2.2.10, p. 66:
    any two functions satisfying its laws agree at every point. *)
Lemma metric_set_distance_unique (R : realType) (T : metricType R)
    (A : set T) d e : is_metric_set_distance A d -> is_metric_set_distance A e ->
  forall x, d x = e x.
Proof.
move=> hd he x; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@metric_set_distance_greatest R T A e he x (d x))=> a ha.
  exact: (@metric_set_distance_lower R T A d hd x a ha).
- apply: (@metric_set_distance_greatest R T A d hd x (e x))=> a ha.
  exact: (@metric_set_distance_lower R T A e he x a ha).
Qed.

(** Source for [metric_set_distance_member]: supporting vanishing
    on the set in Federer 2.2.10, p. 66: if x is in
    A, then the distance from x to A is zero. *)
Lemma metric_set_distance_member (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) x : A x -> d x = 0.
Proof.
move=> hx; apply/eqP; rewrite eq_le (metric_set_distance_nonnegative hd x) andbT.
have h := @metric_set_distance_lower R T A d hd x x hx; by rewrite mdistxx in h.
Qed.

(** Source for [metric_set_distance_subtract_bound]: supporting one-sided
    Lipschitz estimate for Federer 2.2.10, p. 66. *)
Lemma metric_set_distance_subtract_bound (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) x y :
  d x-d y <= mdist x y.
Proof.
rewrite lerBlDr addrC -lerBlDr.
apply: (@metric_set_distance_greatest R T A d hd y (d x-mdist x y))=> a ha.
rewrite lerBlDl; apply: le_trans (@metric_set_distance_lower R T A d hd x a ha) _.
exact: metric_triangle.
Qed.

(** Source for [metric_set_distance_lipschitz_one]: Supporting Federer
    2.2.10, p. 66. *)
Lemma metric_set_distance_lipschitz_one (R : realType) (T : metricType R)
    (A : set T) d (hd : is_metric_set_distance A d) x y :
  `|d x-d y| <= mdist x y.
Proof.
rewrite ler_norml; apply/andP; split.
- rewrite lerNl opprB (metric_sym x y); exact: metric_set_distance_subtract_bound hd y x.
- exact: metric_set_distance_subtract_bound hd x y.
Qed.
