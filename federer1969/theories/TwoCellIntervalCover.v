(** Federer (1969), 2.10.47, p. 204: a set of diameter at most one grid side
    meets a choice of at most two cells in each coordinate. This scalar
    lemma proves the two-cell covering of its coordinate range. The
    n-dimensional bound 2^n follows by taking products of these choices. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ScalarIntervalPartition ScalarIntervalPartitionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [two_grid_cells_cover_short_interval]: supporting
    one-coordinate case of the 2^n cube covering in
    2.10.47, p. 204. The interval may degenerate
    or meet either endpoint of the root interval. The
    two chosen indices may coincide. *)
Theorem two_grid_cells_cover_short_interval (R : realType) k (l u : R) :
  (0<k)%N -> 0<=l -> l<=u -> u<=1 -> u-l<=k%:R^-1 ->
  exists p q : 'I_k, forall x, l<=x<=u ->
    p%:R/k%:R<=x<=p.+1%:R/k%:R \/ q%:R/k%:R<=x<=q.+1%:R/k%:R.
Proof.
move=> hk hl hlu hu hwidth.
pose node := @equal_interval_partition R 1 k ler01 hk.
have hp := @equal_interval_partition_specification R 1 k ler01 hk.
have hl1 : 0<=l<=1 by apply/andP; split=> //; exact: le_trans hlu hu.
have [p /andP [hpl hpu]] := equal_interval_cell_cover hp hl1.
rewrite (equal_interval_node_expansion hp (ltnW (ltn_ord p))) mul1r in hpl.
rewrite (equal_interval_node_expansion hp (ltn_ord p)) mul1r in hpu.
case hlast: (p.+1<k)%N.
- pose q : 'I_k := Ordinal hlast.
  exists p,q=> x /andP [hlx hxu].
  case: (leP x (p.+1%:R/k%:R))=> hx.
  + left; apply/andP; split=> //; exact: le_trans hpl hlx.
  + right; change (is_true (p.+1%:R/k%:R<=x<=p.+2%:R/k%:R)).
    have hs : (p.+2%:R : R)/k%:R=p.+1%:R/k%:R+k%:R^-1.
      by rewrite -addn1 natrD mulrDl mul1r.
    rewrite hs; apply/andP; split; lra.
- have hpk : p.+1=k by apply/eqP; rewrite eqn_leq (ltn_ord p) andTb leqNgt hlast.
  exists p,p=> x /andP [hlx hxu]; left; apply/andP; split.
  + exact: le_trans hpl hlx.
  + rewrite hpk divff; first exact: le_trans hxu hu.
    by rewrite pnatr_eq0 -lt0n.
Qed.
