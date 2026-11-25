(** General normed-space topology supporting Federer (1969), 2.3.8, p. 78.
    The metric comes from a supplied abstract norm; no construction of the
    norm or external measurable-function theorem is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormTopology.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).

(** Source for [real_norm_difference_bound]: supporting triangle estimate
    for norm continuity in Federer 2.3.8, p. 78 *)
Lemma real_norm_difference_bound (x y : V) : N x - N y <= N (x-y).
Proof.
rewrite lerBlDr.
have h := real_seminorm_triangle hN.1 (x-y) y.
by rewrite subrK in h.
Qed.

(** Source for [real_norm_change_bound]: supporting absolute norm
    variation bound for Federer 2.3.8, p. 78; it follows from
    the two triangle inequalities, without completeness. *)
Lemma real_norm_change_bound (x y : V) : `|N x-N y| <= N (x-y).
Proof.
rewrite ler_norml; apply/andP; split.
- rewrite lerNl opprB (real_seminorm_subtract hN.1 x y).
  exact: real_norm_difference_bound.
- exact: real_norm_difference_bound.
Qed.

(** Source for [real_norm_metric_norm_continuous]: continuity of the norm
    used in Federer 2.3.8, p. 78, made explicit. *)
Lemma real_norm_metric_norm_continuous :
  continuous (fun x : M => (N x : real_line_metric R)).
Proof.
move=> x U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (N x : real_line_metric R) U) hU.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP x _)).
exists e=> // y hy; apply: hb.
change (`|N x-N y| < e).
exact: le_lt_trans (real_norm_change_bound x y) hy.
Qed.

(** Source for [real_norm_metric_add_continuous]: continuity of addition
    used to prove closure of the set in Federer 2.3.8, p. 78 *)
Lemma real_norm_metric_add_continuous :
  continuous (fun p : M * M => (p.1+p.2 : M)).
Proof.
move=> [a b] U hU.
have [e he hb] := proj1 (metricType_numDomainType.nbhs_mdistP (a+b : M) U) hU.
have hh : 0 < e/2 by rewrite divr_gt0 // ltr0n.
exists ([set c : M | mdist a c < e/2], [set d : M | mdist b d < e/2]).
- split.
  + apply: (proj2 (metricType_numDomainType.nbhs_mdistP a _)).
    exists (e/2)=> // c hc; exact hc.
  + apply: (proj2 (metricType_numDomainType.nbhs_mdistP b _)).
    exists (e/2)=> // d hd; exact hd.
- move=> [c d] [hc hd]; apply: hb.
  change (N (a+b-(c+d)) < e).
  have -> : a+b-(c+d) = (a-c)+(b-d) by rewrite opprD addrACA.
  apply: le_lt_trans (real_seminorm_triangle hN.1 _ _) _.
  have h := ltrD hc hd; by rewrite -splitr in h.
Qed.
End NormTopology.
