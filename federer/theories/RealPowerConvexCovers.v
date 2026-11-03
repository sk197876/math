(** Federer 2.10.2(1), p. 171: convex generators give the same
    real-degree Hausdorff measure in arbitrary normed vector spaces.
    Convex hulls are used only through their independent inclusion,
    convexity and exact diameter laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import InnerConvex ConvexHull RealNormUP NormMetric
  NormConvexHullDiameter HausdorffLengthUP HausdorffConvexCovers
  RealPowerCoverVariants MetricRealPowerCost MetricRealPowerMeasureUP
  MetricRealPowerMeasure MetricDiameter CaratheodoryTransport
  CaratheodoryMeasure CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_metric_real_power_cover_agreement]: direct
    equality with convex covers in Federer 2.10.2(1),
    p. 171, using hulls in one direction and forgetting
    convexity in the other. Both measures are specified
    independently by their covering laws. *)
Theorem convex_metric_real_power_cover_agreement (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (c p : R) (hc : (0<c)%R)
    (mu nu : set (real_norm_metric_space hN) -> \bar R) :
  is_metric_real_power_measure c p mu -> @is_convex_metric_real_power_measure R V N hN c p nu ->
  forall A, mu A=nu A.
Proof.
move=> hm hn A.
have hle : nu (id @` A)<=mu A.
  apply: (@caratheodory_limit_transport R (real_norm_metric_space hN) (real_norm_metric_space hN)
    (@nonempty_metric_sets R (real_norm_metric_space hN)) (nonempty_convex_sets V)
    (fun j => (val j : set (real_norm_metric_space hN))) (fun j => (val j : set (real_norm_metric_space hN)))
    (fun j => @metric_real_diameter_cost R (real_norm_metric_space hN) c p (val j))
    (fun j => @metric_real_diameter_cost R (real_norm_metric_space hN) c p (val j)) id (@nonempty_convex_hull R V N hN)
    mu nu hm hn _ _ _ _ A).
  - move=> j; exact: metric_real_diameter_cost_ge0 (ltW hc).
  - move=> j x hx; exact: (@convex_hull_includes R V (val j) x hx).
  - move=> j; change (@extended_metric_diameter R (real_norm_metric_space hN) (@convex_hull R V (val j))<=@extended_metric_diameter R (real_norm_metric_space hN) (val j)).
    by rewrite (@extended_metric_diameter_convex_hull R V N hN).
  - move=> j; change (@metric_real_diameter_cost R (real_norm_metric_space hN) c p (@convex_hull R V (val j))<=@metric_real_diameter_cost R (real_norm_metric_space hN) c p (val j)).
    by rewrite /metric_real_diameter_cost (@extended_metric_diameter_convex_hull R V N hN).
have ha : mu (id @` A)<=nu A.
  apply: (@caratheodory_limit_transport R (real_norm_metric_space hN) (real_norm_metric_space hN)
    (nonempty_convex_sets V) (@nonempty_metric_sets R (real_norm_metric_space hN))
    (fun j => (val j : set (real_norm_metric_space hN))) (fun j => (val j : set (real_norm_metric_space hN)))
    (fun j => @metric_real_diameter_cost R (real_norm_metric_space hN) c p (val j))
    (fun j => @metric_real_diameter_cost R (real_norm_metric_space hN) c p (val j)) id (@nonempty_convex_forget R V N hN)
    nu mu hn hm _ _ _ _ A).
  - move=> j; exact: metric_real_diameter_cost_ge0 (ltW hc).
  - by move=> j x hx.
  - by move=> j.
  - by move=> j.
rewrite image_id in hle ha.
by apply/eqP; rewrite eq_le ha hle.
Qed.

(** Source for [metric_real_power_convex_cover_specification]: direct
    assertion that the usual Hausdorff measure is obtained
    from convex covers in Federer 2.10.2(1), p. 171.
    Existence of the competing infimum is supplied by the
    sealed general Caratheodory construction. *)
Theorem metric_real_power_convex_cover_specification (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (c p : R) (hc : (0<c)%R) :
  @is_convex_metric_real_power_measure R V N hN c p (@metric_real_power_measure R (real_norm_metric_space hN) c p).
Proof.
pose S := fun j : nonempty_convex_sets V => (val j : set (real_norm_metric_space hN)).
pose cost := fun j : nonempty_convex_sets V => @metric_real_diameter_cost R (real_norm_metric_space hN) c p (val j).
pose nu := caratheodory_measure S cost.
have hn : @is_convex_metric_real_power_measure R V N hN c p nu := caratheodory_measure_specification S cost.
have he : @metric_real_power_measure R (real_norm_metric_space hN) c p=nu.
  apply: funext=> A; exact (@convex_metric_real_power_cover_agreement R V N hN c p hc _ _
    (@metric_real_power_measure_specification R (real_norm_metric_space hN) c p) hn A).
by rewrite he.
Qed.
