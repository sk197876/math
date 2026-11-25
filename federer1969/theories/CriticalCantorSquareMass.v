(** Federer (1969), 3.2.40, p. 276: actual positive
    product mass of the critical Cantor square. Use the
    previously sealed factor and product measures; no
    fractional Hausdorff normalization is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanRealPlane EuclideanCantorProduct MetricCartesianRectangleBounds
  RealPower RealPowerHalfNatural PowerCantorPairUP PowerCantorIntervalBounds
  PowerCantorProductMeasure MetricRealPowerMeasure MetricDiameterUP MetricDiameter
  MeasureUP MeasureBasic MetricScaleEnvelope MetricScaleMeasureBound
  CaratheodoryLimitUP HausdorffLength HausdorffLengthUP
  HausdorffLengthCompatibility HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_cantor_product_finite_diameter_bound]: supporting
    positive critical size in Federer 3.2.40, p. 276. The actual
    product of the two unit-normalized half-power restrictions
    has mass at most d on every set of diameter at most d>0. *)
Lemma critical_cantor_product_finite_diameter_bound (R:realType)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2))) (d:R):
  is_power_cantor_pair 1 (1/2:R) n A f ->(0<d)%R ->
  extended_metric_diameter S<=d%:E ->
  @power_cantor_product_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A S<=d%:E.
Proof.
move=>hPair hd hDiameter.
pose E:=[the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
pose nu:=@power_cantor_product_measure R E (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
have hNu:=@power_cantor_product_is_measure R E (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
have hm:(0<(1/2:R))%R by lra.
have hm1:((1/2:R)<1)%R by lra.
case:(eqVneq S set0)=>[->|hNonempty].
- rewrite (measure_empty hNu) lee_fin; exact:ltW hd.
- have hS:S !=set0 by apply/set0P.
  have [U [V [hU [hV hCover]]]]:=@metric_cartesian_real_rectangle_hull R E
    (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) S d hS (ltW hd) hDiameter.
  have hRectangle:=@power_cantor_product_rectangle_bound R E
    (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) 1 (1/2:R) ler01 A A S U V hCover.
  have hLeft:=@power_cantor_pair_interval_bound R 1 (1/2:R) n A f ltr01 hm hm1 hPair U.
  have hRight:=@power_cantor_pair_interval_bound R 1 (1/2:R) n A f ltr01 hm hm1 hPair V.
  rewrite hU /= !mul1r in hLeft.
  rewrite hV /= !mul1r in hRight.
  have hHalf:(1/2)%R=((2:R)^-1)%R by rewrite mul1r.
  rewrite -hHalf in hLeft hRight.
  have hNonnegative:=measure_nonnegative
    (@metric_real_power_measure_is_measure R [the metricType R of real_line_metric R] 1 (1/2:R) ler01)
    (A `&` val V).
  have hW:0<=(real_power d (1/2:R))%:E by rewrite lee_fin; exact:real_power_nonnegative.
  have hProduct:=le_trans (lee_wpmul2r hNonnegative hLeft) (lee_wpmul2l hW hRight).
  apply:le_trans hRectangle (le_trans hProduct _).
  rewrite -EFinM (real_power_positive_square_root hd) -expr2 (sqr_sqrtr (ltW hd)).
  exact:lexx.
Qed.

(** Source for [critical_cantor_product_diameter_bound]: supporting
    all-generator comparison for Federer 3.2.40, p. 276.
    Zero diameter uses the already proved null factor law;
    infinite diameter imposes no finite bound. *)
Lemma critical_cantor_product_diameter_bound (R:realType)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R)
    (S:set (inner_metric_space (@euclidean_inner_productP R 2))):
  is_power_cantor_pair 1 (1/2:R) n A f ->
  @power_cantor_product_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A S<=extended_metric_diameter S.
Proof.
move=>hPair.
have hNonnegative:=metric_diameter_nonnegative (extended_metric_diameter_specification S).
case hDiameter:(extended_metric_diameter S) hNonnegative=>[d| |] hNonnegative; [|exact:leey|by []].
have hd:(0<=d)%R by move:hNonnegative; rewrite lee_fin.
case:(eqVneq d (0:R)%R)=>[hZero|hPositive].
- have hm:(0<(1/2:R))%R by lra.
  have hm1:((1/2:R)<1)%R by lra.
  have hD:extended_metric_diameter S=0 by rewrite hDiameter hZero.
  rewrite (@power_cantor_product_zero_diameter R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)]
    (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) 1 (1/2:R) ler01 n n A A f f
    ltr01 hm hm1 hPair hPair S hD) hZero.
  exact:lexx.
- have hdp:(0<d)%R by rewrite lt_neqAle eq_sym hPositive hd.
  apply:critical_cantor_product_finite_diameter_bound hPair hdp _.
  by rewrite hDiameter.
Qed.

(** Source for [critical_cantor_square_Hausdorff_lower_bound]: supporting
    actual positive length at the critical exponent in Federer
    3.2.40, p. 276. The existing product restriction assigns
    mass one to the same-factor square; its proved generator
    bound is dominated by the actual Hausdorff length. *)
Lemma critical_cantor_square_Hausdorff_lower_bound (R:realType)
    (n:nat->nat) (A:set (real_line_metric R)) (f:R->R):
  is_power_cantor_pair 1 (1/2:R) n A f ->
  1<=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (euclidean_cantor_product A A).
Proof.
move=>hPair.
pose E:=[the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
pose W:=euclidean_cantor_product A A.
pose nu:=@power_cantor_product_measure R E (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
have hNu:=@power_cantor_product_is_measure R E (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
have hm:(0<(1/2:R))%R by lra.
have hm1:((1/2:R)<1)%R by lra.
have hMass:nu W= 1.
  have h:=@power_cantor_product_cantor_mass R E
    (@euclidean_real_plane_pair R) (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) 1 (1/2:R) ler01 n n A A f f
    ltr01 hm hm1 hPair hPair.
  by rewrite (mulr1 (1:R)%R) in h.
pose xi:=@metric_scale_envelope R E (@nonempty_metric_sets R E) (fun S=>val S)
  (fun S=>extended_metric_diameter (val S)) 1.
have hXi:=@metric_scale_envelope_specification R E (@nonempty_metric_sets R E) (fun S=>val S)
  (fun S=>extended_metric_diameter (val S)) 1.
have hBound:nu W<=xi W.
  apply:(@measure_bounded_by_metric_scale_envelope R E (@nonempty_metric_sets R E)
    (fun S=>val S) (fun S=>extended_metric_diameter (val S)) 1 xi nu hXi hNu)=>S _.
  exact:critical_cantor_product_diameter_bound hPair.
rewrite hausdorff_measure_one_length -hMass.
apply:le_trans hBound _.
exact:(@caratheodory_limit_upper R E (@nonempty_metric_sets R E) (fun S=>val S)
  (fun S=>extended_metric_diameter (val S)) (@hausdorff_length R E)
  (@hausdorff_length_specification R E) W 1 xi (ltac:(by [])) hXi).
Qed.
