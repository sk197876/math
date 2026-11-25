(** Federer (1969), 2.2.7, p. 64: the complete convex-domain criterion in
    terms of the printed limsup and Lip(f). Source context and the
    nonnegative-bound convention: LipschitzUP.v. All implications use proved
    metric and order-interface results. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerConvex LipschitzUP
  LipschitzBasic LipschitzConstant LocalSlopeBound MetricSlopeLimsup ConvexLocalLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_lipschitz_limsup_criterion]: direct formalisation of
    Federer 2.2.7, p. 64: on a convex subset of a normed space, f is
    Lipschitzian with Lip(f)<=M exactly when every printed local quotient
    limsup is at most M. M is nonnegative; this explicitly includes the
    zero, empty-domain and singleton cases. *)
Theorem convex_lipschitz_limsup_criterion (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (U : metricType R)
    (X : set (real_norm_metric_space hN)) (f : real_norm_metric_space hN -> U) M :
  is_inner_convex X -> 0 <= M ->
  ((exists h : is_metric_lipschitz X f, metric_lipschitz_constant h <= M) <->
    forall x, X x -> (metric_local_slope_limsup X f x <= M%:E)%E).
Proof.
move=> hX hM; split.
- move=> [h hbound]; apply: metric_slope_local_bound_implies_limsup.
  apply: metric_bound_is_local_slope_bound.
  apply: metric_lipschitz_bound_increase _ hbound.
  exact: least_metric_lipschitz_bound (metric_lipschitz_constant_specification h).
- move=> hlim; have hlocal := metric_slope_limsup_implies_local_bound hlim.
  have hb := convex_local_slope_bound_global hX hM hlocal.
  exists (metric_lipschitz_of_bound hb).
  exact: metric_lipschitz_constant_minimal hb.
Qed.
