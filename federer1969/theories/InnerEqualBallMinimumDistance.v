(** Federer (1969), 3.3.19, p. 302: actual
    attained distance between separated equal-radius inner
    metric balls. The auxiliary points stay existential. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  MetricClosedBalls MetricMinimumPairDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_equal_ball_minimum_distance]:
    the actual minimum distance equals centre distance
    minus the two radii, as used in 3.3.19, p. 302.
    Unit directions and attaining points are derived from
    the actual centres, rather than supplied as hypotheses. *)
Theorem inner_equal_ball_minimum_distance (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B)
    (a b:inner_metric_space hB) (r:R):
  0<=r ->2* r<mdist a b ->
  is_metric_minimum_pair_distance (metric_closed_ball a r) (metric_closed_ball b r)
    (mdist a b-2* r).
Proof.
move=>hr hSep;pose d:R:=mdist a b.
have hd:0<d by rewrite /d;lra.
have hdN:d!= 0 by rewrite gt_eqF.
have hInv:0<d^-1 by rewrite invr_gt0.
have hBA:inner_norm hB (b-a)=d.
  have hEq:b-a= -(a-b) by rewrite opprB.
  by rewrite hEq inner_normN /d inner_metric_distanceE.
pose u:inner_metric_space hB:=d^-1*:(b-a).
have hUnit:inner_norm hB u= 1.
  by rewrite /u inner_normZ (ger0_norm (ltW hInv)) hBA mulVf.
have hVector:d*:u=b-a by rewrite /u scalerA mulfV // scale1r.
split.
- move=>x y hx hy.
  have hT:=metric_triangle a x b.
  have hT2:=metric_triangle x y b.
  have hy':mdist y b<=r by rewrite metric_sym;exact hy.
  change (is_true (mdist a x<=r)) in hx.
  rewrite /d;nra.
- pose x:inner_metric_space hB:=a+r*:u.
  pose y:inner_metric_space hB:=b-r*:u.
  have hAX:a-x= -(r*:u) by rewrite /x opprD addrA subrr add0r.
  have hBY:b-y=r*:u by rewrite /y opprB addrC subrK.
  have hx:mdist a x=r by rewrite inner_metric_distanceE hAX inner_normN inner_normZ hUnit mulr1 ger0_norm.
  have hy:mdist b y=r by rewrite inner_metric_distanceE hBY inner_normZ hUnit mulr1 ger0_norm.
  have hYX:y-x=(b-a)-(r+r)*:u.
    by rewrite /y /x opprD addrACA -opprD -scalerDl.
  have hCoefficient:d-(r+r)=d-2* r by ring.
  have hNonnegative:0<=d-2* r by rewrite /d;lra.
  exists x,y;split;first by change (is_true (mdist a x<=r));rewrite hx.
  split;first by change (is_true (mdist b y<=r));rewrite hy.
  have hDistance:mdist y x=d-2* r.
    rewrite (@inner_metric_distanceE R V B hB y x) hYX -hVector -scalerBl hCoefficient
      inner_normZ hUnit mulr1 (ger0_norm hNonnegative).
    exact:erefl.
  by rewrite (metric_sym x y).

Qed.
