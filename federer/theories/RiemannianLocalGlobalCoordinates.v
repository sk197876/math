(** Federer (1969), 3.2.46, p. 282: measure problems
    are localized in the original Riemannian charts. The
    actual metric comparisons and a target-ball extension
    prove suitable global Euclidean representatives on local
    open patches. Coordinate bounds and target containment
    are conclusions, not additional hypotheses on the map. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier RiemannianMapLocalCoordinates
  RiemannianChartOpenImages RiemannianChartReference RiemannianMapCoordinates
  EuclideanBallLipschitzExtension MetricClosedBalls LipschitzUP NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_local_global_coordinate_representative]:
    every actual Lipschitz map between the metric carriers
    agrees locally in the original coordinates with a globally
    Euclidean Lipschitz map whose entire range remains in
    the original target chart, supporting 3.2.46, p. 282.
    The original source patch is an actual ambient open
    subset of A; no global coordinate Lipschitz condition
    or extension staying inside a nonconvex chart is assumed. *)
Theorem riemannian_local_global_coordinate_representative (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_metric_lipschitz setT f -> forall a : riemannian_metric_space hg,
    exists U : set (inner_metric_space (@euclidean_inner_productP R m)),
    exists K : R, exists F : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n),
      open U /\ U (val a) /\ U `<=` A /\ 0<K /\
      is_metric_lipschitz_bound setT F K /\ (forall z, B (F z)) /\
      forall x : riemannian_metric_space hg, U (val x) -> F (val x)=val (f x).
Proof.
move=> hLip a.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
have [V [K [hV [hVa [hK hCoordinateBound]]]]] :=
  @riemannian_map_local_euclidean_bound R m n A B g h hg hh f hLip a.
pose b : E := val (f a).
have [d [hd hDomain]] := @riemannian_tensor_domain_open R n B h hh b (set_valP (f a)).
pose r := d/2.
have hr : 0<r by rewrite /r divr_gt0 // ltr0n.
have hrd : r<d by rewrite /r; lra.
have hBall : metric_closed_ball b r `<=` B.
  move=> y hy.
  have hNorm : inner_norm (@euclidean_inner_productP R n) (y-b)<d.
    apply: le_lt_trans _ hrd.
    by move: hy; rewrite /metric_closed_ball /= (metric_sym b y) inner_metric_distanceE.
  have hY := hDomain (y-b) hNorm.
  by rewrite addrC subrK in hY.
have hCont : continuous f.
  have [c [hc hBound]] := hLip.
  apply: (@metric_fixed_lipschitz_continuous R X Y f c (ltW hc)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
pose p := fun x : X=>(val (f x) : E).
have hPCont : continuous p.
  move=> x; exact (continuous_comp (hCont x) (@riemannian_chart_inclusion_continuous R n B h hh (f x))).
pose W := V `&` (p @^-1` [set y : E | mdist b y<r]).
have hW : open W.
  apply: openI hV _.
  exact (@open_comp X E p [set y : E | mdist b y<r]
    (fun x _=>hPCont x) (@metric_open_ball_open R E b r)).
have hWa : W a.
  split; first exact hVa.
  change (is_true (mdist b b<r)); by rewrite mdistxx.
pose U := (fun x : X=>val x) @` W.
have hU : @open [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] U.
  exact (@riemannian_chart_open_coordinate_image R m A g hg W hW).
have hUa : U (val a) by exists a.
have hUA : U `<=` A by move=> z [x hx <-]; exact: set_valP x.
have [F0 hF0] := @riemannian_coordinate_representative_exists R m n A B g h hg hh f.
have hLocal : @is_metric_lipschitz_bound R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R m)] E U F0 K.
  split; first exact: ltW hK.
  move=> x y [u hu <-] [v hv <-].
  rewrite (hF0 u) (hF0 v).
  exact: hCoordinateBound u v hu.1 hv.1.
have hImage x (hx : U x) : metric_closed_ball b r (F0 x).
  have [u hu <-] := hx; rewrite (hF0 u).
  exact: ltW hu.2.
have [F [hAgreement [hGlobal hRange]]] :=
  @euclidean_chart_lipschitz_extension_exists R m n B U F0 K b r (ltW hr) hBall hLocal hImage.
exists U,K,F; split; first exact hU; split; first exact hUa; split; first exact hUA.
split; first exact hK; split; first exact hGlobal; split; first exact hRange.
move=> x hx; rewrite (hAgreement (val x) hx); exact: hF0.
Qed.
