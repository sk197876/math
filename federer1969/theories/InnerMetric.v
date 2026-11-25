(** Federer (1969), 1.7.1, p. 28: metrisation by |x-y|. The metric laws are
    proved from the inner-product norm laws. MathComp's general
    metric/topological structures are used only to express the topology and
    compactness assertions that follow; no external inner-product or
    orthonormalisation theorem is used. Source context are recorded in
    InnerProductUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import classical_sets topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_metric_space]: Federer 1.7.1,
    p. 28, V equipped with the topology of its specified inner product.
    The carrier is unchanged; the wrapper distinguishes different
    inner products on the same vector space. *)
Definition inner_metric_space (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (_ : is_inner_product B) : Type := V.

HB.instance Definition _ (R : rcfType) (V : lmodType R)
  (B : V -> V -> R) (hB : is_inner_product B) :=
  GRing.Lmodule.copy (inner_metric_space hB) V.

Section Metric.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).

(** Source for [inner_distance]: Federer 1.7.1, p. 28,
    the distance between x and y is |x-y|. *)
Definition inner_distance (x y : M) := inner_norm hB (x-y).

(** Source for [inner_distancexx]: Federer 1.7.1,
    p. 28, supporting metric law: a point has distance zero from itself. *)
Lemma inner_distancexx x : inner_distance x x = 0.
Proof. by rewrite /inner_distance subrr inner_norm0. Qed.

(** Source for [inner_distance_separates]: Federer 1.7.1,
    p. 28, distance zero implies equality of the two points. *)
Lemma inner_distance_separates x y : inner_distance x y = 0 -> x = y.
Proof.
rewrite /inner_distance => h; apply/eqP.
by rewrite -subr_eq0 -(inner_norm_eq0 hB) h eqxx.
Qed.

(** Source for [inner_distance_sym]: Federer 1.7.1,
    p. 28, symmetry of the induced distance. *)
Lemma inner_distance_sym x y : inner_distance x y = inner_distance y x.
Proof. by rewrite /inner_distance -[x-y]opprB inner_normN. Qed.

(** Source for [inner_distance_triangle]: Federer 1.7.1,
    p. 28, the metric triangle inequality follows from the norm triangle inequality. *)
Lemma inner_distance_triangle y x z :
  inner_distance x z <= inner_distance x y + inner_distance y z.
Proof.
rewrite /inner_distance.
have h : x-z = (x-y)+(y-z) by rewrite addrA subrK.
rewrite h; exact: inner_norm_triangle.
Qed.

HB.instance Definition _ := isMetric.Build R M
  inner_distancexx inner_distance_separates inner_distance_sym inner_distance_triangle.

(** Source for [inner_metric_distanceE]: Federer 1.7.1,
    p. 28, the distance of the general metric interface is exactly |x-y|. *)
Lemma inner_metric_distanceE (x y : M) : mdist x y = inner_norm hB (x-y).
Proof. by []. Qed.

(** Source for [inner_distance_nonnegative]: Federer 1.7.1,
    p. 28, the induced distance is nonnegative. *)
Lemma inner_distance_nonnegative x y : 0 <= inner_distance x y.
Proof. exact: inner_norm_nonnegative. Qed.
End Metric.
