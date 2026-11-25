(** Federer (1969), 3.2.35, p. 271:
    the corrected boundary parametrization is actually
    Lipschitz under exactly the original bounded open
    convex-body hypotheses after translation to contain zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  InnerConvex CoveringFamilyUP MinkowskiGaugeUP NormMinkowskiGaugeBounds NormMinkowskiGaugeLipschitz
  NormBoundedZeroOuterBall PositiveReciprocalDifferenceBound NormRadialGaugeMapBound
  RadialGaugeMapUP PartialFunctionUP PartialMetricLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_convex_radial_boundary_lipschitz]:
    the Lipschitz parametrization implicit in the
    boundary rectifiability assertion of Federer 3.2.35,
    p. 271, with erratum p. 5, book p. 271
    line 24. Original openness supplies an inner
    radius r and original boundedness an outer
    radius M. The actual gauge and reciprocal
    inequalities give the finite bound M+M^2/r
    for the exact partial map on the sphere.
    No gauge regularity, radial derivative or bound
    on the map is assumed as an extra premise. *)
Theorem norm_convex_radial_boundary_lipschitz (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) (g:V->R) (f:partial_function V V):
  @is_minkowski_gauge R V S g ->
  @open [the topologicalType of real_norm_metric_space hN] S ->
  is_inner_convex S ->S 0 ->
  @metric_set_bounded R [the metricType R of real_norm_metric_space hN] S ->
  @is_radial_gauge_map R V N g f ->
  exists L:R,@is_partial_metric_lipschitz_bound R
    [the metricType R of real_norm_metric_space hN]
    [the metricType R of real_norm_metric_space hN] f L.
Proof.
move=>hG hOpen hConvex hZero hBound hF.
have [r [hr hRadius]]:=(@norm_domain_interior_neighbourhood R V N hN S 0).2
  (open_nbhs_nbhs (conj hOpen hZero)).
have hBall u:N u<r ->S u.
  move=>hu; have hh:=hRadius u hu; by rewrite add0r in hh.
have [M [hM hOuter]]:=@norm_bounded_zero_outer_ball R V N hN S hBound hZero.
pose C:R:=r^-1.
have hC:0<=C by rewrite /C invr_ge0; exact:ltW hr.
pose L:R:=M+M^+2*C.
have hL:0<=L.
  apply:addr_ge0; first exact:ltW hM.
  exact:(mulr_ge0 (sqr_ge0 M) hC).
have hUnitBounds u (hUnit:N u= 1):0<g u /\(g u)^-1<=M.
  have hLower:=@norm_minkowski_gauge_outer_ball_bound R V N hN S g M hG hM hOuter u.
  rewrite hUnit in hLower.
  exact:(@positive_reciprocal_upper_from_lower R (g u) M hM hLower).
exists L; split; first exact hL.
move=>x y a b hA hB.
have [hX hValueX]:=(@radial_gauge_map_graph_law R V N g f hF x a).1 hA.
have [hY hValueY]:=(@radial_gauge_map_graph_law R V N g f hF y b).1 hB.
have [hGX hInvX]:=hUnitBounds x hX.
have [hGY hInvY]:=hUnitBounds y hY.
change (is_true (N (a-b)<=L*N (x-y))).
rewrite -hValueX -hValueY.
apply:(@norm_radial_gauge_pairwise_bound R V N hN g x y M C
  hX hY hGX hGY hInvX hInvY).
have hScalar:=@norm_minkowski_gauge_lipschitz R V N hN S g r hG hConvex hr hBall x y.
by rewrite /C mulrC.
Qed.
