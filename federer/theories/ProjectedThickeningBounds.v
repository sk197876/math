(** Supporting uniform domination for Federer (1969), 2.10.5(2), p. 173,
    approximation of compact generators by open thickenings. Compactness
    gives a finite source norm bound; all thickenings of radius at most one
    share a bound enlarged by one. The actual projected volumes consequently
    share a finite bound by 2.10.5, p. 172. This uses boundedness of compact
    sets and the triangle inequality of 1.7.1, p. 28, as background, not an
    additional printed measure claim. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm InnerNormInequalities
  InnerNormedTopology ProjectedVolumeBounds ProjectedVolumeMeasurability EuclideanProjectionMetric
  MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_compact_inner_norm_bound]:
    supporting compact source bound in the
    closed convex alternative of Federer 2.10.5(2),
    p. 173. The given metric norm is used
    without introducing a different coordinate norm. *)
Lemma euclidean_compact_inner_norm_bound (R : realType) (n : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact K -> exists c : R, 0<c /\ forall x, K x ->
    inner_norm (@euclidean_inner_productP R n) x<=c.
Proof.
move=> hK; have [M [_ hM]] := compact_bounded hK.
pose c := `|M|+1.
have hc : 0<c by apply: le_lt_trans (normr_ge0 M) _; rewrite /c ltrDl.
have hMc : M<c by apply: le_lt_trans (ler_norm M) _; rewrite ltrDl.
exists c; split=> // x hx.
rewrite -inner_norm_topologyE; exact: (hM c hMc x hx).
Qed.

(** Source for [euclidean_thickening_inner_norm_bound]:
    supporting common dominating bound for the
    open approximations in Federer 2.10.5(2),
    p. 173. Radius at most one increases
    a source norm bound by at most one. *)
Lemma euclidean_thickening_inner_norm_bound (R : realType) (n : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (c r : R) :
  (forall x, K x -> inner_norm (@euclidean_inner_productP R n) x<=c) -> r<=1 ->
  forall x, metric_open_thickening K r x -> inner_norm (@euclidean_inner_productP R n) x<=c+1.
Proof.
move=> hK hr x [a ha hax].
have hd : inner_norm (@euclidean_inner_productP R n) (x-a)<r.
  move: hax; rewrite /= inner_metric_distanceE -[a-x]opprB inner_normN; by [].
have ht := @inner_norm_triangle R _ _ (@euclidean_inner_productP R n) (x-a) a.
rewrite subrK in ht.
apply: le_trans ht _; rewrite addrC; exact: lerD (hK a ha) (le_trans (ltW hd) hr).
Qed.
