(** Federer (1969), 3.2.40, p. 276: positive lower
    Minkowski content of the actual critical Cantor square,
    proved from its existing product measure and finite nets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanRealPlane EuclideanCantorProduct CantorSquareCompactMass
  PowerCantorPairUP PowerCantorPair PowerCantorProductMeasure
  CriticalCantorSquareMass CompactLinearMassTubeLower
  MinkowskiContents EuclideanBallVolume MetricClosedBalls
  EuclideanBallDiameter MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_cantor_square_lower_content_positive]:
    the strict positivity of the critical lower content in
    Federer 3.2.40, p. 276. The actual same-factor square
    carries the previously constructed unit product measure.
    Its proved diameter bound controls every closed ball;
    the compact-net volume argument supplies the full-radius
    lower bound alpha(2)/8. No rectifiability is assumed. *)
Lemma critical_cantor_square_lower_content_positive (R:realType)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  is_power_cantor_pair 1 (1/2:R) n A f ->
  (euclidean_unit_ball_volume R 2/8)%R%:E<=
    lower_minkowski_content 1 (euclidean_cantor_product A A).
Proof.
move=>hPair.
pose E:=[the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
pose W:=euclidean_cantor_product A A.
pose nu:=@power_cantor_product_measure R E (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
have hNu:=@power_cantor_product_is_measure R E (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
have hm:(0<(1/2:R))%R by lra.
have hm1:((1/2:R)<1)%R by lra.
have hA:compact A:=(@power_cantor_pair_properties R 1 (1/2:R) n A f ltr01 hm hm1 hPair).1.
have hW:compact W:=euclidean_cantor_product_compact hA hA.
have hMass:nu W= 1.
  have h:=@power_cantor_product_cantor_mass R E
    (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) 1 (1/2:R) ler01 n n A A f f
    ltr01 hm hm1 hPair hPair.
  by rewrite (mulr1 (1:R)%R) in h.
have hTwo:(0<(2:R))%R by rewrite ltr0n.
have hBall x:W x ->forall t:R,(0<t)%R ->nu (metric_closed_ball x t)<=(2*t)%R%:E.
  move=>_ t ht.
  have hRadius:(0<2*t)%R:=mulr_gt0 hTwo ht.
  apply:(@critical_cantor_product_finite_diameter_bound R n A f (metric_closed_ball x t)
    (2*t)%R hPair hRadius).
  have h:=@metric_ball_diameter_upper R E x t (ltW ht).
  have hDouble:(t+t= 2*t)%R by ring.
  by rewrite hDouble in h.
have hBound:=@compact_linear_mass_lower_minkowski_bound R W nu 2 hW hNu hMass hTwo hBall.
have hEight:((4:R)*2= 8)%R by ring.
by rewrite hEight in hBound.
Qed.
