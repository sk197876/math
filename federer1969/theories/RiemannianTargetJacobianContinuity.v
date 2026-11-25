(** Federer (1969), 3.2.46, p. 282: the
    actual target-degree Jacobian is continuous in both
    original metric points and the actual linear map.
    Frozen coordinates and two-sided distortion prove this
    without a selected continuous frame or derivative field. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  RiemannianTensorUP RiemannianMetricCarrier RiemannianLinearJacobian
  RiemannianLocalTwoMetricJacobian RiemannianChartEllipsoid
  FrozenRiemannianTargetJacobianContinuity LocalMultiplicativeContinuity
  EuclideanHomOperator NormMetric RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_target_jacobian_continuous_parameter]:
    continuity needed to measure the original coarea integrand,
    supporting 3.2.46, p. 282. Continuous source,
    target and operator parameters suffice; no rank condition
    or global linear factor is assumed. *)
Theorem riemannian_target_jacobian_continuous_parameter (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h) (X : topologicalType)
    (p : X -> riemannian_metric_space hg) (q : X -> riemannian_metric_space hh)
    (D : X -> real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)) :
  continuous p -> continuous q -> continuous D ->
  continuous (fun x=>(riemannian_linear_jacobian
    (riemannian_tensor_inner hg (set_valP (p x)))
    (riemannian_tensor_inner hh (set_valP (q x))) n (D x) : real_line_metric R)).
Proof.
move=> hp hq hD.
apply: (@local_multiplicative_continuity R X _ (n+n)).
- move=> x; exact:riemannian_linear_jacobian_nonnegative.
- move=> a lambda hLambda.
  have [L [M [d [e [hd [he [hL [hM [hSource [hTarget hBounds]]]]]]]]]] :=
    @riemannian_local_two_metric_jacobian_bounds R m n A B g h hg hh
      (val (p a)) (set_valP (p a)) (val (q a)) (set_valP (q a)) lambda hLambda.
  exists (fun x=>(riemannian_linear_jacobian
    (riemannian_tensor_inner hg (set_valP (p a)))
    (riemannian_tensor_inner hh (set_valP (q a))) n (D x) : real_line_metric R)).
  split.
  + move=> x; exact (continuous_comp (hD x)
      (@frozen_riemannian_target_jacobian_continuous R m n (g (val (p a)))
        (h (val (q a))) (riemannian_tensor_inner hg (set_valP (p a)))
        (riemannian_tensor_inner hh (set_valP (q a))) (D x))).
  split; first by [].
  pose U := [set z : riemannian_metric_space hg |
    inner_norm (@euclidean_inner_productP R m) (L (val z-val (p a)))<d].
  pose V := [set z : riemannian_metric_space hh |
    inner_norm (@euclidean_inner_productP R n) (M (val z-val (q a)))<e].
  have hUa : U (p a).
    change (is_true (inner_norm (@euclidean_inner_productP R m) (L (val (p a)-val (p a)))<d)).
    by rewrite subrr linear0 inner_norm0.
  have hVa : V (q a).
    change (is_true (inner_norm (@euclidean_inner_productP R n) (M (val (q a)-val (q a)))<e)).
    by rewrite subrr linear0 inner_norm0.
  have hUNear : nbhs a (p @^-1` U).
    exact (hp a _ (open_nbhs_nbhs (conj
      (@riemannian_chart_ellipsoid_open R m A g hg L (val (p a)) d) hUa))).
  have hVNear : nbhs a (q @^-1` V).
    exact (hq a _ (open_nbhs_nbhs (conj
      (@riemannian_chart_ellipsoid_open R n B h hh M (val (q a)) e) hVa))).
  apply: (@filterS X (nbhs a) (nbhs_filter a) _ _ _ (filterI hUNear hVNear))=> x [hx hy].
  exact (hBounds (val (p x)) (set_valP (p x)) (val (q x)) (set_valP (q x))
    (ltW hx) (ltW hy) n (D x)).
Qed.
