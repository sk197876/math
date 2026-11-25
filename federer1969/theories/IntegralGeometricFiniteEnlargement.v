(** Supporting finite-exponent open enlargement for Federer (1969),
    2.10.5(2), p. 173. Compact source thickenings have pointwise convergent
    projected volumes and a common finite bound. Dominated convergence
    therefore gives convergence of the actual finite-t gauges. Choose a late
    enough thickening to control both cost and diameter. This proof does not
    assume the stronger joint compact convex continuity theorem 3.2.36, p.
    272. Exponent infinity requires a separate argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNorm
  InnerConvexNeighbourhoods EuclideanProjectionSpace EuclideanProjectionMetric
  OrthogonalProjectionProbability ProjectedVolumeMeasurability ProjectedVolumeBounds
  ProjectionBeta IntegralGeometricGauge BoundedExtendedNormConvergence
  CompactProjectedVolumeThickening ProjectedThickeningBounds MetricOpenThickening
  ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedRealReciprocalBounds
  RepresentingMeasureComparison BorelClosedProjection TopologicalBorel
  MetricDiameter MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_integral_geometric_finite_thickening_limit]:
    supporting finite-t cost limit for the closed
    convex alternative in Federer 2.10.5(2),
    p. 173. Convexity is unnecessary at this
    step; compactness supplies all domination and
    measurability premises of 2.4.9, p. 85. *)
Theorem compact_integral_geometric_finite_thickening_limit (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (p : R) :
  compact K -> (1<=p)%R -> extended_order_limit
    (fun k => @integral_geometric_gauge R n m hmn p%:E
      (metric_open_thickening K (((k.+1)%:R:R)^-1)%R))
    (@integral_geometric_gauge R n m hmn p%:E K).
Proof.
move=> hK hp.
pose P := orthogonal_projection_metric_space R n m.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose theta := @orthogonal_projection_probability R n m hmn.
pose S k := metric_open_thickening K (((k.+1)%:R:R)^-1)%R.
pose U := metric_open_thickening K 1%R.
have [c [_ hKc]] := euclidean_compact_inner_norm_bound hK.
have hUc : forall x, U x -> (inner_norm (@euclidean_inner_productP R n) x<=c+1)%R.
  exact: euclidean_thickening_inner_norm_bound hKc (lexx 1%R).
have [M [_ hM]] := @projected_volume_function_bounded R n m U (c+1)%R hUc.
have hKU : K `<=` U := metric_open_thickening_includes ltr01.
have hSU k : S k `<=` U.
  move=> x [a ha hax]; exists a=> //.
  change (is_true (mdist a x<1)%R).
  have hrad : (((k.+1)%:R:R)^-1<=1)%R by rewrite invf_le1 ?ler1n // ltr0n.
  exact: lt_le_trans hax hrad.
pose f k (q : P) : extended_real_line R := projected_volume_function (S k) q.
pose g (q : P) : extended_real_line R := projected_volume_function K q.
have hf k := @theta_star_projected_volume_measurable R n m hmn (S k)
  (metric_borel_suslin (open_borel_set (metric_open_thickening_open _ _))).
have hg := @theta_star_projected_volume_measurable R n m hmn K
  (metric_borel_suslin (closed_borel_set (compact_closed (@metric_hausdorff R E) hK))).
have hfn k q : 0<=f k q /\ f k q<=M%:E.
  split; first exact: projected_volume_function_nonnegative.
  exact: le_trans (projected_volume_function_mono q (hSU k)) (hM q).
have hgn q : 0<=g q /\ g q<=M%:E.
  split; first exact: projected_volume_function_nonnegative.
  exact: le_trans (projected_volume_function_mono q hKU) (hM q).
have hl := @bounded_nonnegative_extended_norm_convergence R _ theta
  (@theta_star_is_measure R n m hmn) f g M p (@theta_star_total R n m hmn)
  hp hfn hgn hf hg (fun q => @compact_projected_thickening_volume_limit R n m K q hK).
have hb : (0<(@projection_beta R n m hmn p%:E)^-1)%R.
  rewrite invr_gt0; exact: (@projection_beta_positive R n m hmn p%:E hp).
exact: extended_order_limit_scale hb hl.
Qed.

(** Source for [integral_geometric_finite_convex_open_enlargement]:
    supporting open convex replacement at every
    finite exponent in Federer 2.10.5(2), p. 173.
    Choose the reciprocal radius beyond both the
    cost-convergence threshold and the diameter
    threshold. No uniform projection-parameter
    continuity is assumed. *)
Theorem integral_geometric_finite_convex_open_enlargement (R : realType) (n m : nat)
    (hmn : (m<=n)%N)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (p d t b : R) :
  compact K -> @InnerConvex.is_inner_convex R (R_n R n) K -> (1<=p)%R ->
  (0<=d)%R -> (d<t)%R -> extended_metric_diameter K<=d%:E ->
  @integral_geometric_gauge R n m hmn p%:E K<b%:E ->
  exists U : set (inner_metric_space (@euclidean_inner_productP R n)),
    open U /\ @InnerConvex.is_inner_convex R (R_n R n) U /\ K `<=` U /\
    extended_metric_diameter U<=t%:E /\ @integral_geometric_gauge R n m hmn p%:E U<=b%:E.
Proof.
move=> hK hc hp hd hdt hdiam hb.
have [_ hupper] := @compact_integral_geometric_finite_thickening_limit R n m hmn K p hK hp.
have [N hN] := hupper b%:E hb.
have he : (0<(t-d)/4)%R by rewrite divr_gt0 // subr_gt0.
have [J hJ] := positive_reciprocal_nat_small he.
pose k := (N+J)%N.
pose r : R := (((k.+1)%:R)^-1)%R.
have hr : (0<r)%R by rewrite /r invr_gt0 ltr0n.
have hrsmall : (r<(t-d)/4)%R.
  apply: le_lt_trans _ hJ.
  have hkpos : (0<((k.+1)%:R:R))%R by rewrite ltr0n.
  have hJpos : (0<((J.+1)%:R:R))%R by rewrite ltr0n.
  rewrite /r (@lef_pV2 R (k.+1)%:R (J.+1)%:R hkpos hJpos) ler_nat.
  change (is_true (J<=N+J)%N); exact: leq_addl.
pose U := metric_open_thickening K r.
exists U; split; first exact: metric_open_thickening_open.
split; first exact: (@inner_convex_open_thickening R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) K r hc).
split; first exact: metric_open_thickening_includes hr.
split.
- apply: le_trans (metric_open_thickening_diameter_bound hd (ltW hr) hdiam) _.
  rewrite lee_fin; lra.
- have hNk : (N<=k)%N by rewrite /k leq_addr.
  apply: ltW; exact: hN k hNk.
Qed.
