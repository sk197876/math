(** Federer (1969), 2.2.9, p. 65: the branch point in the nested closures
    E(s)=closure U(s). We use the general closed-intersection theorem from
    2.2.8; no child-cover property is assumed for this open tree. Source
    editions and word convention: OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceTreePrefixes CompleteMetricUP
  ClosedShrinkingIntersection ClosedCoverTreeUP ClosedCoverBranches OpenEmbeddingTreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_embedding_branch_nested]: Federer
    2.2.9, p. 65, nesting of E(n1,...,nk): every child
    closure lies in its parent's open set and hence its closure. *)
Lemma open_embedding_branch_nested (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (n : positive_sequence_space R) i j :
  (i <= j)%N -> closure (U (sequence_tree_prefix n j)) `<=`
    closure (U (sequence_tree_prefix n i)).
Proof.
move=> hij; elim: j hij=> [|j IH] hij x hx.
- have -> : i = 0%N by apply/eqP; rewrite -leqn0.
  exact hx.
- case: (eqVneq i j.+1)=> [->|hine]; first exact hx.
  apply: IH; first by move: hij; rewrite leq_eqVlt (negbTE hine) /= ltnS.
  exact: (@open_embedding_tree_child_closed_inside R T U hU
    (sequence_tree_prefix n j) (positive_sequence_coordinates n j) x hx).
Qed.

(** Source for [open_embedding_branch_shrinks]: Federer
    2.2.9, p. 65: the diameters of successive branch closures
    tend to zero, with the printed strict scale bound. *)
Lemma open_embedding_branch_shrinks (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (n : positive_sequence_space R) e : 0 < e -> exists k,
  forall x y, closure (U (sequence_tree_prefix n k.+1)) x ->
    closure (U (sequence_tree_prefix n k.+1)) y -> mdist x y < e.
Proof.
move=> he; have [k hk] := closed_cover_tree_scale_small he.
exists k=> x y hx hy; apply: lt_trans _ hk.
have hh := open_embedding_tree_diameter hU (s := sequence_tree_prefix n k.+1).
rewrite sequence_tree_prefix_size in hh; apply: hh=> //.
Qed.

(** Source for [open_embedding_branch_point_exists]: Federer 2.2.9, p. 65,
    existence of g(n) by the same complete- space intersection argument as
    in 2.2.8. *)
Theorem open_embedding_branch_point_exists (R : realType) (T : metricType R)
    (hT : is_complete_metric_space T) (U : seq nat -> set T)
    (hU : is_open_embedding_tree U) (n : positive_sequence_space R) :
  exists x, forall k, closure (U (sequence_tree_prefix n k)) x.
Proof.
have hn k : closure (U (sequence_tree_prefix n k.+1)) !=set0.
  have [x hx] := open_embedding_tree_nonempty hU (sequence_tree_prefix n k.+1).
  exists x; exact: subset_closure hx.
have hc k := @closed_closure T (U (sequence_tree_prefix n k.+1)).
have hnest i j : (i <= j)%N ->
    closure (U (sequence_tree_prefix n j.+1)) `<=` closure (U (sequence_tree_prefix n i.+1)).
  move=> hij; exact: (@open_embedding_branch_nested R T U hU n i.+1 j.+1 hij).
have [x hx] := closed_shrinking_metric_intersection hT hn hc hnest
  (@open_embedding_branch_shrinks R T U hU n).
exists x=> k; case: k=> [|k]; last exact: hx.
by rewrite /= (open_embedding_tree_root hU) closureT.
Qed.

(** Source for [open_embedding_branch_point_unique]: Federer
    2.2.9, p. 65, uniqueness of the point on every branch
    from the shrinking diameters, independently of the choice witness. *)
Lemma open_embedding_branch_point_unique (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U)
    (n : positive_sequence_space R) x y :
  (forall k, closure (U (sequence_tree_prefix n k)) x) ->
  (forall k, closure (U (sequence_tree_prefix n k)) y) -> x = y.
Proof.
move=> hx hy; apply: (@shrinking_metric_intersection_unique R T
  (fun k => closure (U (sequence_tree_prefix n k.+1)))
  (@open_embedding_branch_shrinks R T U hU n) x y).
- move=> k; exact: hx.
- move=> k; exact: hy.
Qed.
