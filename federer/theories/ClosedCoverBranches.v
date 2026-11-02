(** Federer (1969), 2.2.8, p. 64: the unique point in the intersection along
    each infinite branch of E. This module uses only the abstract tree laws
    and the locally proved closed-intersection theorem; no computation
    through the tree construction is permitted. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequencePowerBounds ClosedCoverTreeUP
  SequenceTreePrefixes CompleteMetricUP ClosedShrinkingIntersection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_cover_tree_scale_small]: supporting
    limit of the diameter bounds in Federer 2.2.8, p. 64:
    the positive scales 2^(-k-2) tend to zero. *)
Lemma closed_cover_tree_scale_small (R : realType) (e : R) :
  0 < e -> exists n, @closed_cover_tree_scale R n.+1 < e.
Proof.
move=> he; have [n hn] := sequence_inverse_power_small he.
exists n; apply: le_lt_trans _ hn; rewrite /closed_cover_tree_scale.
apply: ler_wiXn2l.
- by rewrite invr_ge0 ler0n.
- by rewrite invf_le1 ?ltr0n // ler1n.
- exact: leq_trans (leqnSn n) (leq_addr _ _).
Qed.

(** Source for [closed_cover_branch_shrinks]: supporting
    shrinking-diameter hypothesis for each branch in Federer
    2.2.8, p. 64, from the abstract tree's level bounds. *)
Lemma closed_cover_branch_shrinks (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_closed_cover_tree E)
    (n : positive_sequence_space R) e : 0 < e -> exists k,
  forall x y, E (sequence_tree_prefix n k.+1) x ->
    E (sequence_tree_prefix n k.+1) y -> mdist x y < e.
Proof.
move=> he; have [k hk] := closed_cover_tree_scale_small he.
exists k=> x y hx hy; apply: le_lt_trans _ hk.
have hh := closed_cover_tree_diameter hE (s := sequence_tree_prefix n k.+1).
rewrite sequence_tree_prefix_size in hh; apply: hh=> //.
Qed.

(** Source for [closed_cover_branch_point_exists]: Federer 2.2.8, p. 64,
    existence of the point called g(n): the intersection of E(n1), E(n1,n2),
    ... is nonempty. The root condition then includes k=0. *)
Theorem closed_cover_branch_point_exists (R : realType) (T : metricType R)
    (hT : is_complete_metric_space T) (E : seq nat -> set T)
    (hE : is_closed_cover_tree E) (n : positive_sequence_space R) :
  exists x, forall k, E (sequence_tree_prefix n k) x.
Proof.
have hn k := closed_cover_tree_nonempty hE (sequence_tree_prefix n k.+1).
have hc k := @closed_cover_tree_closed R T E hE (sequence_tree_prefix n k.+1).
have hnest i j : (i <= j)%N ->
    E (sequence_tree_prefix n j.+1) `<=` E (sequence_tree_prefix n i.+1).
  move=> hij; exact: (@closed_cover_branch_nested R T E hE n i.+1 j.+1 hij).
have [x hx] := closed_shrinking_metric_intersection hT hn hc hnest
  (@closed_cover_branch_shrinks R T E hE n).
exists x=> k; case: k=> [|k]; last exact: hx.
by rewrite /= (closed_cover_tree_root hE).
Qed.

(** Source for [closed_cover_branch_point_unique]: Federer
    2.2.8, p. 64, uniqueness of g(n). Every two branch
    points have distance smaller than every positive number. *)
Lemma closed_cover_branch_point_unique (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_closed_cover_tree E)
    (n : positive_sequence_space R) x y :
  (forall k, E (sequence_tree_prefix n k) x) ->
  (forall k, E (sequence_tree_prefix n k) y) -> x = y.
Proof.
move=> hx hy; apply: (@shrinking_metric_intersection_unique R T
  (fun k => E (sequence_tree_prefix n k.+1))
  (@closed_cover_branch_shrinks R T E hE n) x y).
- move=> k; exact: hx.
- move=> k; exact: hy.
Qed.
