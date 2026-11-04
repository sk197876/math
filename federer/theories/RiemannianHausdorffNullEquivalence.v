(** Federer (1969), 3.2.46, pp. 281–282: ordinary
    and Riemannian Hausdorff measures have the same null
    sets in every real degree. Exact local metric comparison,
    actual linear automorphisms and a countable open cover
    prove this; no completed-measurability equivalence is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  MetricSubsetBackground PositiveSymmetricNormFactor RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianLocalHausdorffComparison RiemannianChartEllipsoid
  RiemannianChartReference RealHausdorffMeasure RealHausdorffNormalisation RealPowerMetricSubset
  EuclideanLinearRealNull MeasureUP MeasureLocalNullTransfer.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_hausdorff_null_iff]: the original
    rho Hausdorff measure vanishes exactly on ordinary
    Hausdorff null sets, in every real degree p>=0,
    supporting the area/coarea assertion in 3.2.46, p. 282.
    Arbitrary nonmeasurable and unbounded sets are retained. *)
Theorem riemannian_hausdorff_null_iff (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) (p : R) (hp : 0<=p)
    (S : set (riemannian_metric_space hg)) :
  (riemannian_hausdorff_measure hg p hp S=0%E <->
   @real_hausdorff_measure R
     [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p hp
     ((fun x : riemannian_metric_space hg=>val x) @` S)=0%E).
Proof.
pose M := [the metricType R of riemannian_metric_space hg].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose C := [the metricType R of @metric_subset R E A].
pose mu := riemannian_hausdorff_measure hg p hp.
pose nu : set M -> \bar R := @real_hausdorff_measure R C p hp.
have hMu := @riemannian_hausdorff_is_measure R n A g hg p hp.
have hNu : is_measure nu := @real_hausdorff_measure_is_measure R C p hp.
have hSubspace B : nu B = @real_hausdorff_measure R E p hp ((fun x : M=>val x) @` B).
  symmetry; exact (@metric_real_power_metric_subset_measure R E A
    (real_hausdorff_normalisation hp) p B
    (ltW (real_hausdorff_normalisation_positive hp)) hp).
have [U hBase] := @riemannian_chart_countable_open_base R n A g hg.
have hLocal a : exists V : set M, open V /\ V a /\ forall T, T `<=` V ->
    (mu T=0%E <->nu T=0%E).
  have hTwo : (1<2 :> R) by rewrite ltr1n.
  have [L [r [hr [hL [hPatch hBounds]]]]] :=
    @riemannian_local_hausdorff_comparison R n A g hg (val a) (set_valP a) 2 hTwo.
  pose V := [set x : M | inner_norm (@euclidean_inner_productP R n) (L (val x-val a))<r].
  exists V; split; first exact: riemannian_chart_ellipsoid_open.
  split; first by rewrite /V /= subrr linear0 inner_norm0.
  move=> T hT.
  have hNear x (hx : T x) : inner_norm (@euclidean_inner_productP R n) (L (val x-val a))<=r.
    exact: ltW (hT x hx).
  have hComparison := hBounds p hp T hNear.
  pose W : set E := (fun x : M=>val x) @` T.
  have hImage : ((fun x : M=>L (val x)) @` T)=(L : E -> E) @` W.
    apply/seteqP; split=> y.
    - move=> [x hx <-]; exists (val x); first by exists x.
      by [].
    - move=> [z [x hx <-] <-]; by exists x.
  rewrite hImage in hComparison.
  have hLinear := @euclidean_linear_real_null_iff R n L p hp W (positive_norm_factor_injective hL).
  split=> hNull.
  - change (riemannian_hausdorff_measure hg p hp T=0%E) in hNull.
    have hBound := hComparison.1; rewrite hNull mule0 in hBound.
    have hImageNull : @real_hausdorff_measure R E p hp (L @` W)=0%E.
      by apply/eqP; rewrite eq_le hBound (measure_nonnegative
        (@real_hausdorff_measure_is_measure R E p hp)).
    rewrite hSubspace; exact: hLinear.1 hImageNull.
  - have hWNull : @real_hausdorff_measure R E p hp W=0%E by rewrite -hSubspace.
    have hImageNull := hLinear.2 hWNull.
    have hBound := hComparison.2; rewrite hImageNull mule0 in hBound.
    by apply/eqP; rewrite eq_le hBound (measure_nonnegative hMu).
rewrite -hSubspace.
split=> hNull.
- apply: (@measure_local_null_transfer R M nu mu U hNu hMu hBase _ S hNull)=> a.
  have [V [hV [ha hC]]] := hLocal a.
  exists V; split; first exact hV; split; first exact ha.
  move=> T hT; exact: (hC T hT).1.
- apply: (@measure_local_null_transfer R M mu nu U hMu hNu hBase _ S hNull)=> a.
  have [V [hV [ha hC]]] := hLocal a.
  exists V; split; first exact hV; split; first exact ha.
  move=> T hT; exact: (hC T hT).2.
Qed.
