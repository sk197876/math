(** Federer (1969), 3.1.1, p. 210: the limit of the inverse-function
    iteration solves x=y-g(x) in the invariant closed ball. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP MetricClosedBalls
  InverseFunctionIterationUP InverseFunctionIteration InverseFunctionIterationBounds
  NormGeometricIncrementLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inverse_function_iteration_solution]: the concluding
    existence step of the iteration argument in Federer 3.1.1, p. 210.
    Completeness yields a limit; closedness keeps it in the ball, and the
    contraction estimate permits passage to the limit in the recurrence. *)
Theorem inverse_function_iteration_solution (R : realType) (X : lmodType R)
    (N : X -> R) (hN : is_real_norm N)
    (hcomplete : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (g : X -> X) (y : X) (c r : R) :
  g 0 = 0 -> 0 < c < 1 -> 0 < r -> N y <= (1-c)*r ->
  (forall x z, N x <= r -> N z <= r -> N (g x-g z) <= c*N (x-z)) ->
  exists x : X, N x <= r /\ x = y-g x.
Proof.
move=> hg0 hc hr hy hg.
pose u := inverse_function_iteration g y.
have hu : is_inverse_function_iteration g y u := inverse_function_iteration_specification g y.
have hc0 : 0 <= c < 1 by apply/andP; split; [exact: ltW (andP hc).1|exact: (andP hc).2].
have hb := @inverse_iteration_ball_bound R X N hN g y u c r hu hg0 hc0 hr hy hg.
have hi := @inverse_iteration_geometric_increments R X N hN g y u c r hu hg0 hc0 hr hy hg.
have [x hx] := @norm_geometric_increments_converge R X N hN hcomplete u c (N y)
  hc (real_seminorm_nonnegative hN.1 y) hi.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have hall : \forall n \near \oo,
    metric_closed_ball (0 : real_norm_metric_space hN) r (u n).
  exists 0%N=> // n _.
  change (N (0-u n) <= r); rewrite sub0r (real_seminorm_negate hN.1); exact: (hb n).2.
have hball := @closed_cvg nat (real_norm_metric_space hN) \oo PF0 u
  (metric_closed_ball (0 : real_norm_metric_space hN) r)
  (@metric_closed_ball_closed R [the metricType R of real_norm_metric_space hN] 0 r)
  hall x hx.
have hxr : N x <= r.
  change (is_true (N (0-x) <= r)) in hball.
  by rewrite sub0r (real_seminorm_negate hN.1) in hball.
exists x; split=> //.
have herror : forall e : R, 0 < e -> N (x-(y-g x)) < e.
  move=> e he.
  have hc1 : 0 < c+1 by have := (andP hc).1; lra.
  pose d := e/(2*(c+1)).
  have hd : 0 < d by rewrite /d divr_gt0 // mulr_gt0 // ltr0n.
  have hevent : \forall n \near \oo,
      ball (x : real_norm_metric_space hN) d (u n).
    exact: (cvg_ballP _ _).1 hx d hd.
  have [k _ hk] := hevent.
  have hkn := hk k (leqnn k).
  have hks := hk k.+1 (leqnSn k).
  rewrite !ballEmdist /= in hkn hks.
  change (is_true (N (x-u k) < d)) in hkn.
  change (is_true (N (x-u k.+1) < d)) in hks.
  have hgb := hg (u k) x (hb k).2 hxr.
  rewrite [N (u k-x)](real_seminorm_subtract hN.1) in hgb.
  have heq : x-(y-g x) = (x-u k.+1)+(g x-g (u k)).
    rewrite (inverse_iteration_step hu).
    by rewrite !opprB !addrA [x+g (u k)-y]addrAC
      [x-y+g (u k)+g x]addrAC addrK [x+g x-y]addrAC.
  have htri : N (x-(y-g x)) <= N (x-u k.+1)+N (g (u k)-g x).
    rewrite {1}heq; apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
    by rewrite [N (g x-g (u k))](real_seminorm_subtract hN.1).
  have hbound : c*N (x-u k) < c*d by rewrite ltr_pM2l //; exact: (andP hc).1.
  have hden : 0 < 2*(c+1) by rewrite mulr_gt0 // ltr0n.
  have heqcoef : d*(2*(c+1)) = e by rewrite /d divfK //; exact: lt0r_neq0 hden.
  have hcoef : (c+1)*d = e/2 by nra.
  by nra.
have hz : N (x-(y-g x)) = 0.
  apply/eqP; rewrite eq_le; apply/andP; split; last exact: real_seminorm_nonnegative hN.1 _.
  apply/ler_addgt0Pr=> e he; rewrite add0r; exact: ltW (herror e he).
have hh := hN.2 _ hz; by move/eqP: hh; rewrite subr_eq0=> /eqP.
Qed.
