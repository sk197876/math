(** Federer (1969), 3.1.12, pp. 223–224:
    supporting identification of disjoint balls with their centers.
    Unlike general metric balls, nonempty norm balls have unique centers. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Centers.
Variable R : realType.
Variable V : lmodType R.
Variable B : V->V->R.
Hypothesis hB : is_inner_product B.
Local Notation X := (inner_metric_space hB).

(** Source for [inner_closed_ball_inclusion_center_bound]:
    supporting passage from the disjoint set family of Federer
    3.1.12, p. 223, to its indexing by centers. A
    containing ball must reach the point on the opposite center ray. *)
Lemma inner_closed_ball_inclusion_center_bound (a b : X) (r s : R) :
  0<=r -> a!=b -> metric_closed_ball a r `<=` metric_closed_ball b s ->
  r+mdist a b<=s.
Proof.
move=>hr hab hsub.
pose d := inner_norm hB (a-b).
have hd : 0<d by rewrite /d inner_norm_gt0 subr_eq0.
have hc : 0<=r/d by rewrite divr_ge0 //; exact: ltW hd.
pose x := a+(r/d)*:(a-b).
have hxa : x-a=(r/d)*:(a-b) by rewrite /x addrAC subrr add0r.
have hxb : x-b=(1+r/d)*:(a-b).
  rewrite /x scalerDl scale1r.
  by rewrite addrAC.
have hax : mdist a x=r.
  rewrite metric_sym inner_metric_distanceE hxa inner_normZ (ger0_norm hc).
  by rewrite /d divfK // gt_eqF.
have hbx : mdist b x=r+d.
  have hc1 : 0<=1+r/d by exact: addr_ge0 ler01 hc.
  rewrite metric_sym inner_metric_distanceE hxb inner_normZ (ger0_norm hc1).
  change ((1+r/d)*d=r+d).
  by rewrite mulrDl mul1r divfK // ?gt_eqF // addrC.
have hx : metric_closed_ball a r x by change (mdist a x<=r); rewrite hax.
have hh := hsub x hx.
change (is_true (mdist b x<=s)) in hh.
by rewrite hbx in hh; rewrite inner_metric_distanceE.
Qed.

(** Source for [inner_closed_ball_center_unique]: equal
    nonempty closed balls have the same center, supporting the
    set-family convention of Federer 3.1.12, p. 223.
    This includes the zero-dimensional source. *)
Lemma inner_closed_ball_center_unique (a b : X) (r s : R) :
  0<=r -> 0<=s -> metric_closed_ball a r=metric_closed_ball b s -> a=b.
Proof.
move=>hr hs he; case:(eqVneq a b)=>[hab|hab]; first exact hab.
have hsub : metric_closed_ball a r `<=` metric_closed_ball b s by rewrite he.
have hsub' : metric_closed_ball b s `<=` metric_closed_ball a r by rewrite he.
have hp := inner_closed_ball_inclusion_center_bound hr hab hsub.
have hba : b!=a by rewrite eq_sym.
have hq := inner_closed_ball_inclusion_center_bound hs hba hsub'.
rewrite metric_sym in hq.
have hd : 0<mdist a b by rewrite inner_metric_distanceE inner_norm_gt0 subr_eq0.
exfalso; nra.
Qed.
End Centers.
