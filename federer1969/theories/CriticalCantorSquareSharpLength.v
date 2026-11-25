(** Federer (1969), 3.3.20, pp. 308–309: the exact Hausdorff length of the original critical square. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground EuclideanRealPlane
  EuclideanCantorProduct PowerCantorPairUP PowerCantorCarrierCoefficient PowerCantorProductMeasure
  BinaryCantorSquareLevelsUP CriticalSquareHitMeasureExistence CriticalSquareProductHitBound
  CriticalPositiveDiameterAttainment CantorSquareCompactMass RealPowerHalfNatural
  MetricDiameterUP MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleMeasureBound
  CaratheodoryLimitUP HausdorffLengthUP HausdorffLength HausdorffLengthCompatibility HausdorffMeasure
  MeasureUP MeasureBasic MeasureRestriction FiniteMeasureScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_original_cantor_square_sharp_length]: the
    exact H^1(E)=sqrt(2) conclusion of 3.3.20, pp. 308–309, for the
    original binary quarter Cantor square. The actual unit product
    restriction, scaled by sqrt(2), is bounded by every original psi_j.
    The proved positive-diameter finite-stage comparison and separate
    zero-diameter nullity give the bound for every actual Hausdorff
    generator. No optimal Frostman estimate or measurability premise is
    supplied. The upper bound is the original square cover. *)
Theorem critical_original_cantor_square_sharp_length (R:realType) (c:R)
    (A:set (real_line_metric R)) (f:R->R):
  (0<c)%R ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (euclidean_cantor_product A A)=(Num.sqrt (2:R))%:E.
Proof.
move=>hc hPair.
have hm:(0<(1/2:R))%R by lra.
have hm1:((1/2:R)<1)%R by lra.
have [g hUnit]:=@power_cantor_carrier_coefficient_change R c 1 (1/2:R)
  (fun _:nat=>2%N) A f hc ltr01 hm hm1 hPair.
have [J [H [hJ [hTree [hA _]]]]]:=hPair.
have [G hG]:=binary_cantor_square_levels_exist H.
have [psi [hPsi _]]:=critical_square_hit_measures_exist G.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose E:=euclidean_cantor_product A A.
pose nu:=@power_cantor_product_measure R [the metricType R of X]
  (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
have hNu:is_measure nu:=@power_cantor_product_is_measure R X
  (@euclidean_real_plane_pair R) 1 (1/2:R) ler01 A A.
pose mu:=fun T:set X=>(Num.sqrt (2:R))%:E * nu (E `&` T).
have hMu:is_measure mu:=finite_scale_is_measure (measure_restrict_is_measure hNu E) (sqrtr_ge0 _).
have hMass:mu E=(Num.sqrt (2:R))%:E.
  have h:=@power_cantor_product_cantor_mass R X (@euclidean_real_plane_pair R)
    (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
    (@euclidean_real_plane_is_metric_product R) 1 (1/2:R) ler01
    (fun _:nat=>2%N) (fun _:nat=>2%N) A A g g ltr01 hm hm1 hUnit hUnit.
  by rewrite /mu setIid /nu h mul1r mule1.
have hGenerator (T:nonempty_metric_sets X):extended_metric_diameter (val T)<=1 ->
    mu (val T)<=extended_metric_diameter (val T).
  move=>hDiameter.
  have hNonnegative:=metric_diameter_nonnegative (extended_metric_diameter_specification (val T)).
  case hD:(extended_metric_diameter (val T)) hNonnegative hDiameter=>[d| |] hd hd1;last 2 first.
  - by rewrite leye_eq in hd1.
  - by [].
  have hd0:(0<=d)%R by move:hd;rewrite lee_fin.
  case:(eqVneq d (0:R)%R)=>hZero.
  - have hDZero:extended_metric_diameter (val T)=0 by rewrite hD hZero.
    have hNull:=@power_cantor_product_zero_diameter R X (@euclidean_real_plane_pair R)
      (@euclidean_real_plane_first R) (@euclidean_real_plane_second R)
      (@euclidean_real_plane_is_metric_product R) 1 (1/2:R) ler01
      (fun _:nat=>2%N) (fun _:nat=>2%N) A A g g ltr01 hm hm1 hUnit hUnit (val T) hDZero.
    have hSubset:E `&` val T `<=` val T by move=>x [].
    change (nu (val T)=0) in hNull.
    have hBound:=measure_mono hNu hSubset.
    rewrite hNull in hBound.
    have hRestricted:nu (E `&` val T)=0.
      apply/eqP;rewrite eq_le hBound;exact:measure_nonnegative hNu _.
    by rewrite /mu hRestricted mule0 hZero.
  - have hdPositive:(0<d)%R by rewrite lt_neqAle eq_sym hZero hd0.
    have [j hj]:=@critical_original_positive_diameter_attainment R c d J H G psi A (val T)
      hc hdPositive hJ hTree hA hG hPsi (ltac:(by rewrite hD)).
    have hHit:=@critical_square_original_product_hit_bound R c J H G A psi
      hc hJ hTree hA hG hPsi j (val T).
    exact:le_trans hHit hj.
pose xi:=@metric_scale_envelope R [the metricType R of X] (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>extended_metric_diameter (val S)) 1.
have hXi:=@metric_scale_envelope_specification R [the metricType R of X] (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>extended_metric_diameter (val S)) 1.
have hLower:=@measure_bounded_by_metric_scale_envelope R X (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>extended_metric_diameter (val S)) 1 xi mu hXi hMu hGenerator E.
rewrite hMass in hLower.
have hLimit:=@caratheodory_limit_upper R X (@nonempty_metric_sets R X)
  (fun S=>val S) (fun S=>extended_metric_diameter (val S)) _
  (@hausdorff_length_specification R X) E 1 xi (ltac:(by [])) hXi.
have hFinalLower:=le_trans hLower hLimit.
rewrite -hausdorff_measure_one_length in hFinalLower.
have hUpper:=@critical_cantor_square_Hausdorff_upper_bound R c (fun _:nat=>2%N) A f hc hPair.
rewrite (@real_power_positive_square_root R 2 (ltac:(by rewrite ltr0n))) in hUpper.
apply/eqP;rewrite eq_le hUpper hFinalLower;by [].
Qed.
