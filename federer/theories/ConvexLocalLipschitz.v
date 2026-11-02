(** Federer (1969), 2.2.7, p. 64, the convex-domain local quotient
    criterion. The local upper-limit hypothesis is expressed by eventual
    bounds above every L>M; see LocalSlopeBound.v. We require M nonnegative,
    as is necessary for a bound on the nonnegative optimal constant,
    including empty and singleton domains. The proof uses the printed
    segment and supremum argument through IntervalLocalBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerConvex
  LipschitzUP LipschitzBasic LocalSlopeBound IntervalLocalBound ConvexMetricSegment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_local_slope_bound_global]: Federer 2.2.7, p. 64,
    sufficiency of the local upper-limit condition on a convex normed-space
    domain. For every L>M apply the printed supremum argument along
    a+t(b-a), then let L decrease to M. *)
Theorem convex_local_slope_bound_global (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (U : metricType R)
    (X : set (real_norm_metric_space hN)) (f : real_norm_metric_space hN -> U) M :
  is_inner_convex X -> 0 <= M -> is_metric_local_slope_bound X f M ->
  is_metric_lipschitz_bound X f M.
Proof.
move=> hX hM hlocal; split=> // a b ha hb.
case: (eqVneq a b)=> [->|hab]; first by rewrite !mdistxx mulr0.
have hD : 0 < N (b-a).
  rewrite (real_norm_positive hN.1 hN.2) subr_eq0 eq_sym; exact hab.
have hfor L : M < L -> mdist (f a) (f b) <= L * N (b-a).
  move=> hL.
  have hLp : 0 < L := le_lt_trans hM hL.
  pose g t := f (metric_segment_point a b t).
  have hC : 0 <= L * N (b-a) by rewrite mulr_ge0 ?ltW.
  have hg : forall r, 0 <= r -> r <= 1 -> exists d, 0 < d /\
      forall t, 0 <= t -> t <= 1 -> `|t-r| < d ->
        mdist (g r) (g t) <= (L * N (b-a)) * `|t-r|.
    move=> r hr0 hr1.
    have hrX := metric_segment_in_convex hX ha hb hr0 hr1.
    have [d [hd hstep]] := hlocal _ hrX L hL.
    exists (d / N (b-a)); split; first by rewrite divr_gt0.
    move=> t ht0 ht1 ht.
    have htX := metric_segment_in_convex hX ha hb ht0 ht1.
    have hdist : mdist (metric_segment_point a b r) (metric_segment_point a b t) < d.
      rewrite metric_segment_distance -[r-t]opprB normrN.
      by rewrite -(ltr_pdivlMr _ _ hD).
    have hh := hstep _ htX hdist.
    rewrite metric_segment_distance -[r-t]opprB normrN [`|t-r| * N (b-a)]mulrC mulrA in hh.
    exact hh.
  have hh := interval_local_metric_bound hC hg.
  by rewrite /g metric_segment_zero metric_segment_one in hh.
rewrite real_norm_metric_distanceE (real_seminorm_subtract hN.1 a b).
rewrite -(ler_pdivrMr _ _ hD).
apply/ler_addgt0Pr=> e he.
rewrite (ler_pdivrMr _ _ hD); apply: hfor.
by rewrite ltrDl.
Qed.

(** Source for [convex_lipschitz_local_slope_equivalence]: Federer
    2.2.7, p. 64, direct equivalence between a global bound M
    and the local upper-limit condition on a convex normed domain.
    M is nonnegative; finite zero bounds are included. *)
Theorem convex_lipschitz_local_slope_equivalence (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (U : metricType R)
    (X : set (real_norm_metric_space hN)) (f : real_norm_metric_space hN -> U) M :
  is_inner_convex X -> 0 <= M ->
  (is_metric_lipschitz_bound X f M <-> is_metric_local_slope_bound X f M).
Proof.
move=> hX hM; split; first exact: metric_bound_is_local_slope_bound.
exact: convex_local_slope_bound_global hX hM.
Qed.
