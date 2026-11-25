(** Federer (1969), 3.2.46, pp. 281–282: local
    frozen inner-product comparisons reduce Riemannian
    Lipschitz maps to Euclidean Lipschitz coordinate maps.
    The proof uses the actual metric carriers and local
    existential frames; no coordinate Lipschitz bound or
    globally selected frame field is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier RiemannianLocalMetricComparison
  RiemannianChartEllipsoid PositiveNormFactorBound EuclideanLinearRealNull
  LipschitzUP NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_local_euclidean_bound]:
    every actual Lipschitz map of the metric carriers has
    finite positive Euclidean coordinate bounds on an open
    neighbourhood of each original source point, supporting
    3.2.46, p. 282, from the local inequalities on p. 281.
    The technical finite metrics agree with original rho
    on the comparison patches. Zero dimensions, disconnected
    charts and singular maps are not excluded. *)
Theorem riemannian_map_local_euclidean_bound (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_metric_lipschitz setT f -> forall a,
    exists V : set (riemannian_metric_space hg), exists K : R,
      open V /\ V a /\ 0<K /\ forall x y, V x -> V y ->
      mdist (val (f x) : inner_metric_space (@euclidean_inner_productP R n)) (val (f y)) <=
        K*mdist (val x : inner_metric_space (@euclidean_inner_productP R m)) (val y).
Proof.
move=> [c [hc hBound]] a.
pose X := [the metricType R of riemannian_metric_space hg].
pose Y := [the metricType R of riemannian_metric_space hh].
have hTwo : (1<2 :> R) by rewrite ltr1n.
have hTwo0 : (0<2 :> R) by rewrite ltr0n.
have hTwoNe : (2 : R)!=0 := lt0r_neq0 hTwo0.
have [L [r [hr [hL [hSourcePatch hSource]]]]] :=
  @riemannian_local_metric_comparison R m A g hg (val a) (set_valP a) 2 hTwo.
have [M [s [hs [hM [hTargetPatch hTarget]]]]] :=
  @riemannian_local_metric_comparison R n B h hh (val (f a)) (set_valP (f a)) 2 hTwo.
have [Ki [hKi hInverse]] := positive_norm_factor_inverse_bound hM.
have [Ks [hKs hLinear]] := euclidean_positive_linear_metric_bound L.
pose V0 := [set x : X | inner_norm (@euclidean_inner_productP R m) (L (val x-val a))<r].
pose W := [set y : Y | inner_norm (@euclidean_inner_productP R n) (M (val y-val (f a)))<s].
have hV0 : open V0 := @riemannian_chart_ellipsoid_open R m A g hg L (val a) r.
have hW : open W := @riemannian_chart_ellipsoid_open R n B h hh M (val (f a)) s.
have hCont : continuous f.
  apply: (@metric_fixed_lipschitz_continuous R X Y f c (ltW hc)).
  by move=> x y; exact: hBound.2 x y Logic.I Logic.I.
pose V := V0 `&` (f @^-1` W).
pose K := Ki*2*c*2*Ks.
exists V,K; split.
- apply: openI hV0 _; exact (@open_comp X Y f W (fun x _=>hCont x) hW).
- split.
  + split.
    * change (is_true (inner_norm (@euclidean_inner_productP R m) (L (val a-val a))<r)).
      by rewrite subrr linear0 inner_norm0.
    * change (is_true (inner_norm (@euclidean_inner_productP R n) (M (val (f a)-val (f a)))<s)).
      by rewrite subrr linear0 inner_norm0.
  + split; first by rewrite /K !mulr_gt0.
    move=> x y hx hy.
    have hxL := ltW hx.1; have hyL := ltW hy.1.
    have hxM := ltW hx.2; have hyM := ltW hy.2.
    have hSourceUpper := (hSource y x hyL hxL).2.
    rewrite (metric_sym y x) in hSourceUpper.
    have hTargetLower := (hTarget (f y) (f x) hyM hxM).1.
    rewrite (metric_sym (f y) (f x)) in hTargetLower.
    have hNormal : inner_norm (@euclidean_inner_productP R n) (M (val (f x)-val (f y)))<=
        2*mdist (f x) (f y).
      have hScaled := ler_wpM2l (ltW hTwo0) hTargetLower.
      by rewrite mulrA mulfV // mul1r in hScaled.
    have hLip := hBound.2 x y Logic.I Logic.I.
    have hLs : inner_norm (@euclidean_inner_productP R m) (L (val x-val y))<=
        Ks*inner_norm (@euclidean_inner_productP R m) (val x-val y).
      have hLinearPoint := hLinear.2 (val x-val y) 0 Logic.I Logic.I.
      change (is_true (inner_norm (@euclidean_inner_productP R m) (L (val x-val y)-L 0)<=
        Ks*inner_norm (@euclidean_inner_productP R m) ((val x-val y)-0))) in hLinearPoint.
      by rewrite linear0 !subr0 in hLinearPoint.
    rewrite !inner_metric_distanceE /K.
    apply: le_trans (hInverse (val (f x)-val (f y))) _.
    apply: le_trans (ler_wpM2l (ltW hKi) hNormal) _.
    apply: le_trans (ler_wpM2l (ltW hKi) (ler_wpM2l (ltW hTwo0) hLip)) _.
    apply: le_trans (ler_wpM2l (ltW hKi) (ler_wpM2l (ltW hTwo0)
      (ler_wpM2l (ltW hc) hSourceUpper))) _.
    have hLast := ler_wpM2l (ltW hKi) (ler_wpM2l (ltW hTwo0)
      (ler_wpM2l (ltW hc) (ler_wpM2l (ltW hTwo0) hLs))).
    rewrite !mulrA; by rewrite !mulrA in hLast.
Qed.
