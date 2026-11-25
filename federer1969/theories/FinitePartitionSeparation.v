(** The finite-subset step in the fibre-counting limit of Federer (1969),
    2.10.10, p. 176. A fine enough partition separates any prescribed finite
    collection of points. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals topology.
From Federer Require Import ClosedCoverTreeUP CoverPartitionTreeUP
  BorelImageTreeEquality ShrinkingBorelPartitionLevels FiniteMetricSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [finite_points_partition_separation]:
    finitely many distinct fibre points eventually lie in
    distinct partition cells, supporting the increasing limit
    in Federer 2.10.10, p. 176. The
    map assigns every ambient point a cell at one positive
    level and is injective on the prescribed finite set. *)
Lemma finite_points_partition_separation (R : realType) (X : metricType R)
    (E P : seq nat -> set X) (hE : is_closed_cover_tree E)
    (hP : is_cover_partition_tree E P) (B : {fset X}) :
  exists n (g : X -> seq nat),
    (forall x, size (g x)=n.+1 /\ P (g x) x) /\
    (forall x y, x \in B -> y \in B -> g x=g y -> x=y).
Proof.
have [e [he hsep]] := finite_metric_points_separated B.
have [n hn] := closed_cover_tree_scale_small he.
have hex x := @cover_partition_level_membership R X E P hE hP x n.+1.
pose g x := projT1 (cid (hex x)).
have hg x : size (g x)=n.+1 /\ P (g x) x := projT2 (cid (hex x)).
exists n, g; split=> // x y hx hy hxy.
apply/eqP; apply/negPn/negP=> hne.
have hs : g x !=[::] by rewrite -size_eq0 (hg x).1.
have hycell : P (g x) y by rewrite hxy; exact: (hg y).2.
have hd := @cover_partition_level_diameter R X E P hE hP (g x) x y hs (hg x).2 hycell.
rewrite (hg x).1 in hd.
have hlt := le_lt_trans hd hn.
by move: hlt; rewrite ltNge (hsep x y hx hy hne).
Qed.
