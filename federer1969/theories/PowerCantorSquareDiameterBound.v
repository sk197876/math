(** Federer (1969), 3.3.20, p. 306: actual lower
    real-degree mass of the original product, expanding
    the printed 2.10.27 appeal without a normalization premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanRealPlane EuclideanCantorProduct MetricCartesianRectangleBounds
  RealPower RealPowerSuccessor PowerCantorPairUP PowerCantorIntervalBounds
  PowerCantorProductMeasure MetricRealPowerMeasure MetricDiameterUP MetricDiameter
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_square_finite_diameter_bound]:
    the actual unit product restriction has mass at most
    d^(2m) on every original set of diameter at most
    positive finite d, for every 0<m<1. This supplies
    the lower bound in 3.3.20, p. 306. Actual
    coordinate interval hulls and factor bounds retain
    arbitrary original test sets and the actual product. *)
Lemma power_cantor_square_finite_diameter_bound (R:realType)
    (m:R) (n:nat->nat) (A:set (real_line_metric R)) (f:R->R)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2))) (d:R):
  (0<m)%R ->(m<1)%R ->is_power_cantor_pair 1 m n A f ->(0<d)%R ->
  extended_metric_diameter S<=d%:E ->
  @power_cantor_product_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    (@euclidean_real_plane_pair R) 1 m ler01 A A S<=(real_power d (2* m))%:E.
Proof.
move=>hm hm1 hPair hd hDiameter.
pose E:=[the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
pose nu:=@power_cantor_product_measure R E (@euclidean_real_plane_pair R) 1 m ler01 A A.
have hNu:=@power_cantor_product_is_measure R E (@euclidean_real_plane_pair R) 1 m ler01 A A.
case:(eqVneq S set0)=>[->|hNonempty].
- rewrite (measure_empty hNu) lee_fin;exact:real_power_nonnegative.
- have hS:S !=set0 by apply/set0P.
  have [U [V [hU [hV hCover]]]]:=@metric_cartesian_real_rectangle_hull R E
    (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) S d hS (ltW hd) hDiameter.
  have hRectangle:=@power_cantor_product_rectangle_bound R E
    (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) 1 m ler01 A A S U V hCover.
  have hLeft:=@power_cantor_pair_interval_bound R 1 m n A f ltr01 hm hm1 hPair U.
  have hRight:=@power_cantor_pair_interval_bound R 1 m n A f ltr01 hm hm1 hPair V.
  rewrite hU /= !mul1r in hLeft.
  rewrite hV /= !mul1r in hRight.
  have hNonnegative:=measure_nonnegative
    (@metric_real_power_measure_is_measure R [the metricType R of real_line_metric R] 1 m ler01)
    (A `&` val V).
  have hW:0<=(real_power d m)%:E by rewrite lee_fin; exact:real_power_nonnegative.
  have hProduct:=le_trans (lee_wpmul2r hNonnegative hLeft) (lee_wpmul2l hW hRight).
  apply:le_trans hRectangle (le_trans hProduct _).
  rewrite -EFinM.
  have hTwice:(2* m=m+m)%R by ring.
  by rewrite hTwice real_power_add_exponents_positive.
Qed.
