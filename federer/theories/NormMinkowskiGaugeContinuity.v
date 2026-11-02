(** Federer (1969), 3.2.35, p. 271:
    continuity of the actual convex gauge and
    closedness of its unit sublevel support the
    corrected boundary parametrization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology num_normedtype.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity RealMetricBackground
  InnerConvex MinkowskiGaugeUP NormMinkowskiGaugeLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_minkowski_gauge_continuous]:
    supporting continuity of g in the radial
    argument of Federer 3.2.35, p. 271.
    The proved pairwise bound from an original
    inner ball yields continuity for the actual
    norm and scalar topologies. The independent
    gauge laws retain the original vector-space type. *)
Lemma norm_minkowski_gauge_continuous (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) (g:V->R) r:
  @is_minkowski_gauge R V S g ->is_inner_convex S ->0<r ->
  (forall y:V,N y<r ->S y) ->
  continuous (g:real_norm_metric_space hN->real_line_metric R).
Proof.
move=>hG hConvex hr hBall.
have hC:0<=r^-1 by rewrite invr_ge0; exact:ltW hr.
apply:(@metric_fixed_lipschitz_continuous R
  [the metricType R of real_norm_metric_space hN]
  [the metricType R of real_line_metric R] g r^-1 hC).
move=>x y; change (is_true (`|g x-g y|<=r^-1*N (x-y))).
have hBound:=@norm_minkowski_gauge_lipschitz R V N hN S g r hG hConvex hr hBall x y.
by rewrite mulrC.
Qed.

(** Source for [norm_minkowski_gauge_closed_unit_sublevel]:
    the closed unit gauge sublevel used to
    identify the boundary in Federer 3.2.35,
    p. 271. Actual continuity and the scalar
    closed half-line give closedness; the subsequent
    equality with the original set closure is a
    separate theorem, not a premise here. *)
Lemma norm_minkowski_gauge_closed_unit_sublevel (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) (g:V->R) r:
  @is_minkowski_gauge R V S g ->is_inner_convex S ->0<r ->
  (forall y:V,N y<r ->S y) ->
  @closed [the topologicalType of real_norm_metric_space hN] [set x|g x<=1].
Proof.
move=>hG hConvex hr hBall.
have hCont:=@norm_minkowski_gauge_continuous R V N hN S g r hG hConvex hr hBall.
change (@closed [the topologicalType of real_norm_metric_space hN]
  ((g:real_norm_metric_space hN->real_line_metric R) @^-1` [set t:real_line_metric R|t<=1])).
apply:preimage_closed; last exact:closed_le.
by move=>x _; exact:(hCont x).
Qed.
