(** Federer (1969), 3.2.42, printed p. 278:
    the outer distance tube is the actual sum of the source
    with the open ball about zero. This identity also retains
    empty sources, without assigning them a finite distance. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology num_normedtype.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology
  VectorSetSum MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_ball_vector_sum_tube]: direct first
    identity in the proof of Federer 3.2.42, p. 278, before
    replacing the source by its closure. Every original
    centre and increment are retained; arbitrary sources,
    empty sets and all natural ambient dimensions remain. *)
Lemma euclidean_ball_vector_sum_tube (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  metric_open_thickening S r=
    vector_set_sum S [set y | `|y|<r].
Proof.
apply/seteqP; split=> z.
- move=>[a ha hNear]; apply/vector_set_sum_membership.
  exists a,(z-a); split; first exact ha.
  split.
  + change (is_true (`|z-a|<r)); by rewrite -inner_metric_normE.
  + by rewrite addrC subrK.
- move=>/vector_set_sum_membership [a [b [ha [hb ->]]]].
  exists a=>//.
  change (is_true (mdist a (a+b)<r)).
  by rewrite inner_metric_normE addrC addKr.
Qed.
