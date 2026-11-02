(** Federer (1969), 3.2.36, p. 272:
    the actual Steiner polynomial bounds small
    tube-volume increments without assumptions
    about continuity of its coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricSetDistanceUP SteinerTubePolynomial ConvexSteinerTubeFormula SteinerTubeScalarPolynomial
  SteinerReversePolynomialBound ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge
  FullDimensionIntegralGauge EuclideanBallVolume EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [convex_small_tube_volume_increment]:
    supporting the first deduction of Federer
    3.2.36, p. 272, from 3.2.35.
    For every original nonempty bounded convex
    source and radius 0<r<=1, its tube
    volume is at most its original volume
    plus r times its actual unit-tube volume.
    Nonnegative finite coefficients give this
    bound before any varying-body continuity
    assertion. All natural dimensions and
    arbitrary original source measurability remain. *)
Theorem convex_small_tube_volume_increment (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d (r:R):
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->
  (0<r)%R ->(r<=1)%R ->
  euclidean_lebesgue_measure n [set x|(d x<r)%R]<=euclidean_lebesgue_measure n S+
    r%:E*euclidean_lebesgue_measure n [set x|(d x<1)%R].
Proof.
move=>hNonempty hS hBound hD hr hr1.
pose a (i:'I_n.+1):R:=(fine (@integral_geometric_gauge R n i (steiner_dimension_guard i) 1 S)*
  euclidean_unit_ball_volume R (n-i))%R.
have ha i:(0<=a i)%R.
  exact:steiner_tube_scalar_coefficient_nonnegative hNonempty hS hBound.
have hScalar t:steiner_tube_polynomial S t=(\sum_i a i*t^+(n-i))%R%:E.
  rewrite (steiner_tube_polynomial_scalar_value t hNonempty hS hBound).
  congr (_%:E); apply:eq_bigr=>i _; by rewrite /a mulrA.
have hConstant:(a ord_max)%:E=euclidean_lebesgue_measure n S.
  have [hZero hFinite]:=@convex_intrinsic_volume_nonnegative_finite R n ord_max
    (steiner_dimension_guard ord_max) 1 S hNonempty hS hBound (lexx 1).
  have hFinNum:@integral_geometric_gauge R n ord_max (steiner_dimension_guard ord_max) 1 S \is a fin_num.
    by rewrite (ge0_fin_numE hZero).
  rewrite /a subnn euclidean_unit_ball_volume0 mulr1 (fineK hFinNum).
  exact:(@equal_dimension_integral_geometric_gauge R n _ 1 S (lexx 1)).
have hFormula:=convex_steiner_tube_formula hNonempty hS hBound hD.
have hUnit:(\sum_i a i)%R%:E=euclidean_lebesgue_measure n [set x|(d x<1)%R].
  rewrite (hFormula 1%R ltr01) hScalar; congr (_%:E).
  apply:eq_bigr=>i _; by rewrite expr1n mulr1.
rewrite (hFormula r hr) hScalar -hConstant -hUnit -EFinM -EFinD lee_fin.
exact:nonnegative_reverse_polynomial_small_radius_bound ha (ltW hr) hr1.
Qed.
