(** General topology supporting Federer (1969), 2.2.10, p. 65: X times N is
    a complete separable metric space when X is. This adapter equips the
    existing Cartesian product topology with the maximum of its two given
    distances. These are supporting metric facts, not a new distance
    prescribed by Federer. Source context: SuslinSetUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_product]: supporting Cartesian product
    carrier for Federer 2.2.10, p. 65. The existing product
    topology is retained, and the explicit metric is added on
    this wrapper to avoid changing canonical background instances. *)
Definition metric_product (R : realType) (T U : metricType R) : Type := (T * U)%type.
HB.instance Definition _ (R : realType) (T U : metricType R) :=
  PseudoMetric.copy (metric_product T U) (T * U)%type.

Section ProductMetric.
Context (R : realType) (T U : metricType R).
Local Notation M := (metric_product T U).

(** Source for [metric_product_distance_nonnegative]: metric
    background for Federer 2.2.10, p. 65: the maximum
    of the two nonnegative factor distances is nonnegative. *)
Lemma metric_product_distance_nonnegative (x y : M) :
  0 <= Order.max (mdist x.1 y.1) (mdist x.2 y.2).
Proof. by rewrite le_max mdist_ge0. Qed.

(** Source for [metric_product_distance_separates]: metric
    background for Federer 2.2.10, p. 65: zero maximum
    distance forces equality in both factors. *)
Lemma metric_product_distance_separates (x y : M) :
  Order.max (mdist x.1 y.1) (mdist x.2 y.2) = 0 -> x = y.
Proof.
move=> hz; have hle : Order.max (mdist x.1 y.1) (mdist x.2 y.2) <= 0 by rewrite hz.
move: hle; rewrite ge_max=> /andP [h1 h2].
have he1 : mdist x.1 y.1 = 0 by apply/eqP; rewrite eq_le h1 mdist_ge0.
have he2 : mdist x.2 y.2 = 0 by apply/eqP; rewrite eq_le h2 mdist_ge0.
have hx := @mdist_positivity R T x.1 y.1 he1;
have hy := @mdist_positivity R U x.2 y.2 he2.
exact: (@injective_projections T U x y hx hy).
Qed.

(** Source for [metric_product_ball_distance]: product-topology
    compatibility supporting Federer 2.2.10, p. 65:
    a maximum-distance ball is the product of the factor balls. *)
Lemma metric_product_ball_distance (x : M) r :
  ball x r = [set y : M | Order.max (mdist x.1 y.1) (mdist x.2 y.2) < r].
Proof.
apply/seteqP; split=> y.
- change ((ball x.1 r y.1 /\ ball x.2 r y.2) ->
    Order.max (mdist x.1 y.1) (mdist x.2 y.2) < r).
  rewrite !ballEmdist /= gt_max; by move=> [h1 h2]; apply/andP.
- change (Order.max (mdist x.1 y.1) (mdist x.2 y.2) < r ->
    (ball x.1 r y.1 /\ ball x.2 r y.2)).
  rewrite !ballEmdist /= gt_max; by move/andP.
Qed.
HB.instance Definition _ := PseudoMetric_isMetric.Build R M
  metric_product_distance_nonnegative metric_product_distance_separates metric_product_ball_distance.

(** Source for [metric_product_distanceE]: exposed product metric
    identity supporting Federer 2.2.10, p. 65. *)
Lemma metric_product_distanceE (x y : M) :
  mdist x y = Order.max (mdist x.1 y.1) (mdist x.2 y.2).
Proof. by []. Qed.
End ProductMetric.
