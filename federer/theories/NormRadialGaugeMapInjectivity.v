(** Federer (1969), 3.3.19, p. 304: support
    for ordering the original convex-boundary points.
    The corrected radial sphere map of 3.2.35,
    p. 271, is injective on its actual domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import RealNormUP NormMetric InnerConvex CoveringFamilyUP
  MinkowskiGaugeUP NormMinkowskiGaugeBounds NormBoundedZeroOuterBall
  RadialGaugeMapUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_radial_gauge_map_positive_injective]:
    supporting injectivity of the actual radial boundary
    map used in the cyclic ordering of 3.3.19,
    p. 304. Positive radial factors and actual
    unit norms recover the original direction. *)
Lemma norm_radial_gauge_map_positive_injective (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (g:V->R) (f:partial_function V V):
  @is_radial_gauge_map R V N g f ->
  (forall x,N x= 1 ->0<g x) ->
  forall x y z,partial_function_graph f x z ->partial_function_graph f y z ->x= y.
Proof.
move=>hF hPositive x y z hx hy.
have [hX hValueX]:=(@radial_gauge_map_graph_law R V N g f hF x z).1 hx.
have [hY hValueY]:=(@radial_gauge_map_graph_law R V N g f hF y z).1 hy.
have hGX:= hPositive x hX;have hGY:= hPositive y hY.
have hInvX:0< (g x)^-1 by rewrite invr_gt0.
have hInvY:0< (g y)^-1 by rewrite invr_gt0.
have hImage:(g x)^-1 *: x=(g y)^-1 *: y by rewrite hValueX hValueY.
have hNormX:N ((g x)^-1 *: x)=(g x)^-1.
  by rewrite (real_seminorm_scale hN.1) hX mulr1 (ger0_norm (ltW hInvX)).
have hNormY:N ((g y)^-1 *: y)=(g y)^-1.
  by rewrite (real_seminorm_scale hN.1) hY mulr1 (ger0_norm (ltW hInvY)).
have hInv:(g x)^-1=(g y)^-1 by rewrite -hNormX -hNormY hImage.
rewrite -hInv in hImage.
apply:(scalerI (lt0r_neq0 hInvX));exact hImage.
Qed.

(** Source for [norm_convex_radial_boundary_injective]:
    no injectivity premise is needed for the original
    bounded open convex body in the boundary-cycle
    argument of 3.3.19, p. 304.
    Original boundedness and gauge laws prove every
    radial factor positive before applying norm cancellation. *)
Theorem norm_convex_radial_boundary_injective (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) (g:V->R) (f:partial_function V V):
  @is_minkowski_gauge R V S g ->S 0 ->
  @metric_set_bounded R [the metricType R of real_norm_metric_space hN] S ->
  @is_radial_gauge_map R V N g f ->
  forall x y z,partial_function_graph f x z ->partial_function_graph f y z ->x= y.
Proof.
move=>hG hZero hBound hF.
have [M [hM hOuter]]:= @norm_bounded_zero_outer_ball R V N hN S hBound hZero.
apply:(@norm_radial_gauge_map_positive_injective R V N hN g f hF)=>x hX.
have hLower:= @norm_minkowski_gauge_outer_ball_bound R V N hN S g M hG hM hOuter x.
rewrite hX div1r in hLower.
have hInv:0<M^-1 by rewrite invr_gt0.
exact:(lt_le_trans hInv hLower).
Qed.
