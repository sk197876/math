(** Federer (1969), 2.10.39, printed p. 199: the equal side subdivisions
    cover their whole side, including endpoints, and each cell fits in an
    interval centred at its midpoint. These consequences use only the
    abstract node laws, not a node implementation. Source context and
    spherical context: ScalarSubdivisionCount.v and
    ScalarIntervalPartitionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import ScalarIntervalPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Partition.
Variable R : realType.
Variable c : R.
Variable k : nat.
Variable node : nat -> R.
Hypothesis hP : is_equal_interval_partition c k node.

(** Source for [equal_interval_node_expansion]: supporting
    coordinate formula for the equal subdivision in
    2.10.39, p. 199, derived from its initial
    node and step laws. Only constrained nodes are used. *)
Lemma equal_interval_node_expansion i : (i<=k)%N -> node i= i%:R*(c/k%:R).
Proof.
elim: i=> [|i IH] hik; first by rewrite (equal_interval_initial_law hP) mul0r.
have hprev : (i<=k)%N := leq_trans (leqnSn i) hik.
have hh := equal_interval_step_law hP hik.
have he : node i.+1=node i+c/k%:R by lra.
by rewrite he (IH hprev) -addn1 natrD mulrDl mul1r.
Qed.

(** Source for [equal_interval_cell_cover]: supporting
    finite covering by the equal cells in 2.10.39,
    p. 199. A least-crossing argument retains both
    closed endpoints and also permits a zero side length. *)
Theorem equal_interval_cell_cover x : 0<=x<=c ->
  exists j : 'I_k, node j<=x<=node j.+1.
Proof.
move=> /andP [hx0 hxc].
have hk := equal_interval_count_positive_law hP.
have hlast : x<=node k.-1.+1 by rewrite (prednK hk) (equal_interval_final_law hP).
have hex : exists j : nat, x<=node j.+1 by exists k.-1.
have [j hj hmin] := ex_minnP hex.
have hpred : (k.-1<k)%N by rewrite (prednK hk).
have hjk : (j<k)%N := leq_ltn_trans (hmin k.-1 hlast) hpred.
have hlo : node j<=x.
  case: (eqVneq j 0)=> [->|hj0]; first by rewrite (equal_interval_initial_law hP).
  have hjpos : (0<j)%N by rewrite lt0n.
  rewrite leNgt; apply/negP=> hbad.
  have hp : x<=node j.-1.+1 by rewrite (prednK hjpos); exact: ltW hbad.
  have hjpred : (j.-1<j)%N by rewrite (prednK hjpos).
  have hn := leq_ltn_trans (hmin j.-1 hp) hjpred.
  by rewrite ltnn in hn.
exists (Ordinal hjk); exact/andP.
Qed.

(** Source for [equal_interval_midpoint_cover]: supporting
    midpoint covering of each subdivided box side in
    2.10.39, p. 199. When its cell width
    is at most h, every point is within h/2
    of some cell midpoint, including at a cell endpoint. *)
Theorem equal_interval_midpoint_cover (h x : R) :
  c/k%:R<=h -> 0<=x<=c -> exists j : 'I_k,
    `|x-(node j+node j.+1)/2|<=h/2.
Proof.
move=> hw hx; have [j /andP [hlo hhi]] := equal_interval_cell_cover hx.
have hs := equal_interval_step_law hP (ltn_ord j).
exists j; rewrite ler_norml; apply/andP; split; lra.
Qed.
End Partition.
