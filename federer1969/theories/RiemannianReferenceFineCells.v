(** Federer (1969), 3.2.46, p. 281: arbitrarily small
    ordinary chart balls have positive finite Lebesgue mass,
    so the pointwise volume-ratio derivative has a genuine
    fine partial domain. Dimension zero retains its unit atom. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric MetricSubsetBackground MetricClosedBalls MetricDiameterUP MetricDiameter
  EuclideanLebesgueDimensions EuclideanClosedBallGrowth EuclideanClosedBallVolume
  EuclideanBallVolume RiemannianTensorUP RiemannianMetricCarrier RiemannianChartReference
  ContinuousPositiveDensityDerivate CoveringRelationUP CoveringRelationFineness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_reference_fine_positive_cells]:
    the denominator domain of the actual derivate in 3.2.46,
    p. 281, is fine at every original chart point.
    Actual small closed Euclidean balls supply its witnesses,
    with no assumption that the Riemannian measure is globally
    finite on all Euclidean bounded subsets of the chart. *)
Lemma riemannian_reference_fine_positive_cells (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (a : @metric_subset R [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] A) :
  @covering_relation_fine_at R
    [the metricType R of @metric_subset R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] A]
    (positive_finite_containing_relation (@riemannian_chart_reference R n A g hg)) a.
Proof.
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose C := [the metricType R of @metric_subset R E A].
apply: (covering_relation_fine_iff_small_diameter _ a).2=> e he.
have [d [hd hA]] := @riemannian_tensor_domain_open R n A g hg (val a) (set_valP a).
pose r := Num.min (e/4) (d/2).
have hr : 0<r by rewrite /r lt_min !divr_gt0 // !ltr0n.
have hre : r<=e/4 by rewrite /r ge_min lexx.
have hrd : r<=d/2 by rewrite /r ge_min lexx orbT.
have hrdStrict : r<d by lra.
have hDiameter : r+r<e by lra.
pose D := metric_closed_ball (val a : E) r.
pose S : set C := (fun x : C=>val x) @^-1` D.
have hDA : D `<=` A.
  move=> x hx.
  have hNorm : inner_norm (@euclidean_inner_productP R n) (x-val a)<=r.
    move: hx; rewrite /D /metric_closed_ball /= (metric_sym (val a) x) inner_metric_distanceE; by [].
  have hIn := hA (x-val a) (le_lt_trans hNorm hrdStrict).
  by rewrite addrC subrK in hIn.
have hImage : (fun x : C=>(val x : E)) @` S=D.
  apply/seteqP; split=> x.
  - by move=> [y hy <-].
  - move=> hx; exists (@exist E (fun z=>z \in (A : set E)) x (mem_set (hDA x hx))); by [].
have hMass : @riemannian_chart_reference R n A g hg S =
    (euclidean_unit_ball_volume R n*r^+n)%:E.
  rewrite riemannian_chart_reference_value hImage.
  exact: euclidean_closed_ball_normalized_volume (ltW hr).
have hPositive : 0<euclidean_unit_ball_volume R n*r^+n.
  exact: mulr_gt0 (euclidean_unit_ball_volumeE R n).2 (exprn_gt0 n hr).
exists S; split.
- split.
  + change (is_true (mdist (val a : E) (val a)<=r)).
    by rewrite mdistxx; exact: ltW hr.
  + split; rewrite hMass; first by rewrite lte_fin.
    by [].
- apply: le_lt_trans _ _.
  + apply: (@metric_diameter_least R C S (extended_metric_diameter S)
      (extended_metric_diameter_specification S) (r+r)%:E).
    * rewrite lee_fin; exact: addr_ge0 (ltW hr) (ltW hr).
    * move=> x y hx hy; rewrite lee_fin metric_subset_distanceE.
      exact: metric_closed_ball_diameter_bound hx hy.
  + by rewrite lte_fin.
Qed.
