(** Federer (1969), 3.2.35, p. 271:
    the corrected radial map has exactly the
    boundary of the original bounded open convex body
    as its image. All auxiliary gauge positivity is proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealNormUP NormMetric InnerConvex CoveringFamilyUP
  MinkowskiGaugeUP MinkowskiGaugeAbsorption NormMinkowskiGaugeBounds NormBoundedZeroOuterBall
  NormOpenConvexMinkowskiBoundary RadialGaugeMapUP RadialGaugeMapExistence RadialGaugeMapUnitLevel
  PartialFunctionUP PartialMetricLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_convex_radial_boundary_image]:
    the corrected boundary image display of Federer
    3.2.35, p. 271, with erratum p. 5,
    book p. 271 line 24: g(x)^(-1)x.
    Actual boundedness supplies a positive outer radius;
    the independent gauge laws give strict positivity
    at every unit vector. The actual unit-level
    image and proved boundary identity then give
    both image inclusions without a positivity or
    boundary-parametrization premise. *)
Theorem norm_convex_radial_boundary_image (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) (g:V->R) (f:partial_function V V):
  @is_minkowski_gauge R V S g ->
  @open [the topologicalType of real_norm_metric_space hN] S ->
  is_inner_convex S ->S 0 ->
  @metric_set_bounded R [the metricType R of real_norm_metric_space hN] S ->
  @is_radial_gauge_map R V N g f ->
  partial_function_range f=(@closure [the topologicalType of real_norm_metric_space hN] S `\`
    @interior [the topologicalType of real_norm_metric_space hN] S).
Proof.
move=>hG hOpen hConvex hZero hBound hF.
have [M [hM hOuter]]:=@norm_bounded_zero_outer_ball R V N hN S hBound hZero.
have hPositive u:N u= 1 ->0<g u.
  move=>hUnit.
  have hLower:=@norm_minkowski_gauge_outer_ball_bound R V N hN S g M hG hM hOuter u.
  rewrite hUnit mul1r in hLower.
  have hInv:0<M^-1 by rewrite invr_gt0.
  exact:(lt_le_trans hInv hLower).
rewrite (@radial_gauge_map_unit_level R V N hN S g f hG hZero hF hPositive).
apply/seteqP; split=>y hy.
- exact:((@norm_open_convex_minkowski_boundary R V N hN S g hG hOpen hConvex hZero y).2 hy).
- exact:((@norm_open_convex_minkowski_boundary R V N hN S g hG hOpen hConvex hZero y).1 hy).
Qed.

(** Source for [norm_convex_radial_boundary_map_exists]:
    supporting existence of the corrected boundary
    parametrization in Federer 3.2.35, p. 271.
    Original openness constructs a gauge satisfying
    its independent infimum laws; the independent
    sphere-map laws have a proved local witness.
    The original boundedness then proves its exact
    boundary image. No global gauge or map is chosen. *)
Theorem norm_convex_radial_boundary_map_exists (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V):
  @open [the topologicalType of real_norm_metric_space hN] S ->
  is_inner_convex S ->S 0 ->
  @metric_set_bounded R [the metricType R of real_norm_metric_space hN] S ->
  exists (g:V->R) (f:partial_function V V),
    @is_minkowski_gauge R V S g /\@is_radial_gauge_map R V N g f /\
    partial_function_range f=(@closure [the topologicalType of real_norm_metric_space hN] S `\`
      @interior [the topologicalType of real_norm_metric_space hN] S).
Proof.
move=>hOpen hConvex hZero hBound.
have [g hG]:=@norm_open_minkowski_gauge_exists R V N hN S hOpen hZero.
have [f hF]:=@radial_gauge_map_exists R V N g.
exists g,f; split; first exact hG; split; first exact hF.
exact:(@norm_convex_radial_boundary_image R V N hN S g f hG hOpen hConvex hZero hBound hF).
Qed.
