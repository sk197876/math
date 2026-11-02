(** Federer (1969), 2.10.46, pp. 203–204: the Gross upper product bound,
    first with finite first-factor volume and finite positive second-factor
    measure. Cover the first factor by sufficiently small balls, use the
    second-factor cutoff estimate, then let the relative scale tend to zero.
    No measurability of either factor is required. This file records only
    this finite-value case, not the opposite inequality or the remaining
    endpoint cases. Source context and inputs: GrossBallProductCutoff.v and
    SmallBallLebesgueComparison.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanBlockCoordinates
  MetricProductRectangles MetricClosedBalls EuclideanLebesgueDimensions ProjectionMeasure
  ProjectedVolumeGauge BorelCoverCostUP CaratheodoryLimitUP MetricScaleCutoffCost
  MeasureUP MeasureRestriction MeasurePushforward GrossBallProductCutoff
  SmallBallLebesgueComparison PolynomialMarginLimit ExtendedRealOrderTopology ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [gross_finite_product_upper_bound]: finite positive
    second-factor case of the Gross upper inequality asserted in
    2.10.46, pp. 203–204. The first dimension is positive;
    the first volume may be zero. Explicit finite values keep
    the limiting arithmetic separate from endpoint cases. *)
Theorem gross_finite_product_upper_bound (R : realType) m n k
    (U : set (inner_metric_space (@euclidean_inner_productP R m.+1)))
    (V : set (inner_metric_space (@euclidean_inner_productP R n))) (u v : R) :
  (k<=n)%N -> 0<=u -> 0<v -> euclidean_lebesgue_measure m.+1 U=u%:E ->
  @gross_measure R n k V=v%:E ->
  (@gross_measure R (m.+1+n) (m.+1+k) (metric_product_rectangle
    (fun z=>(@euclidean_block_split R m.+1 n z).1)
    (fun z=>(@euclidean_block_split R m.+1 n z).2) U V)<=(u*v)%:E)%E.
Proof.
move=> hkn hu hv hU hV.
pose P := [the metricType R of inner_metric_space (@euclidean_inner_productP R (m.+1+n))].
pose X := [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)].
pose Y := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose first := fun z=>(@euclidean_block_split R m.+1 n z).1.
pose second := fun z=>(@euclidean_block_split R m.+1 n z).2.
have hdim : (m.+1+k<=m.+1+n)%N by rewrite leq_add2l.
apply: (caratheodory_limit_least (gross_measure_specification R (m.+1+n) (m.+1+k)))=> delta nu hdelta hn.
have [q [hq hqd]] := @extended_rationals_order_dense R 0%E delta hdelta.
have hq0 : (0<ratr q :>R) by move: hq; rewrite lte_fin.
have hnu : is_measure nu.
  apply: (metric_scale_envelope_is_measure hn)=> j.
  exact: projected_volume_gauge_nonnegative hdim.
pose rho := fun A : set X=>nu (metric_product_rectangle first second A V).
have hrho : is_measure rho.
  have heq : rho=measure_pushforward first (measure_restrict nu (second @^-1` V)).
    by apply: funext=> A; rewrite /rho /metric_product_rectangle /measure_pushforward /measure_restrict setIC.
  rewrite heq; exact: measure_pushforward_is_measure (measure_restrict_is_measure hnu _).
have hb : (rho U<=((u*v)*1^+m.+1)%:E)%E.
  apply: (@nonnegative_polynomial_margin_limit R m.+1 1 1 (u*v) (rho U)
    ler01 ltr01 (mulr_ge0 hu (ltW hv)))=> e he _.
  pose s := Num.sqrt (1+e^+2).
  have hsq : 0<1+e^+2 by have hh := sqr_ge0 e; lra.
  have hs : 0<s by rewrite /s sqrtr_gt0.
  pose cap := ratr q/(s+s).
  have hss : 0<s+s := addr_gt0 hs hs.
  have hcap : 0<cap := divr_gt0 hq0 hss.
  have hcaprel : cap*(s+s)=ratr q by rewrite /cap divfK //; exact: lt0r_neq0 hss.
  pose b := s^+m.+1*v.
  have hbpos : 0<b := mulr_gt0 (exprn_gt0 _ hs) hv.
  have hball a r : 0<r -> r<=cap ->
      (rho (metric_closed_ball a r)<=b%:E*euclidean_lebesgue_measure m.+1 (metric_closed_ball a r))%E.
    move=> hr hrcap.
    have hd : (((r+r)*s)%:E<=delta)%E.
      apply: le_trans _ (ltW hqd); rewrite lee_fin.
      have hnon := ltW hs; nra.
    have hh := @gross_ball_product_cutoff_bound R m.+1 n k a r e V delta nu hkn hr he hd hn.
    rewrite hV -/s in hh.
    have heq : (b%:E*euclidean_lebesgue_measure m.+1 (metric_closed_ball a r))%E=
      (euclidean_lebesgue_measure m.+1 (metric_closed_ball a r)*(s^+m.+1)%:E*v%:E)%E.
      by rewrite /b EFinM muleC muleA.
    rewrite heq; exact hh.
  have hh := @small_ball_measure_lebesgue_bound R m rho b cap hrho hbpos hcap hball U.
  rewrite hU -EFinM in hh.
  apply: le_trans hh _; rewrite lee_fin.
  have hse : s<=1+e.
    rewrite -(ler_sqr (ltW hs) (addr_ge0 ler01 (ltW he))) /s sqr_sqrtr; last exact: ltW hsq.
    nra.
  have hp : s^+m.+1<=(1+e)^+m.+1 by apply: lerXn2r=> //; [exact: ltW hs|exact: addr_ge0 ler01 (ltW he)].
  have hmul : (u*v)*s^+m.+1<=(u*v)*(1+e)^+m.+1.
    have hnon := mulr_ge0 hu (ltW hv); nra.
  have heq : b*u=(u*v)*s^+m.+1 by rewrite /b; ring.
  rewrite heq; exact hmul.
by rewrite expr1n mulr1 in hb.
Qed.
