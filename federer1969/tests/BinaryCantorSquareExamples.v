(** Federer (1969), 3.3.20, pp. 306–309: actual original-object regressions. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct BinaryCantorSetUP BinaryCantorSetSealed BinaryCantorSquareExample
  BinaryCantorSquareLevelsUP CriticalSquareHitMeasureUP CriticalSquareHitMeasureExistence
  CriticalSquareZeroDiameterQualification CriticalAllDirectionProjectionVolume CriticalProjectionScalarBound
  HausdorffMeasure ProjectionMeasure IntegralGeometricMeasure RealHausdorffMeasure RealHausdorffNormalisation
  MetricDiameter MetricDiameterMaps LebesgueScalarMeasure.
From Federer Require Import BinaryCantorSquareHits.
From Federer Require Import BinaryFirstAllDirectionProjection.
From Federer Require Import BinaryOriginalBorelPartitions.
From Federer Require Import BinaryProjectionCoefficientFullLocus.
From Federer Require Import BinaryUniformProjectionCoefficient.
From Federer Require Import CriticalOriginalProjectionBound.
From Federer Require Import CriticalOriginalProjectionPartitions.
From Federer Require Import CriticalSquareHitMonotonicity.
From Federer Require Import PlanarDiagonalDistanceBound.
From Federer Require Import PowerCantorSquarePositiveFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_square_actual_critical_measure_values]: the
    actual opaque original critical E has Hausdorff length sqrt(2)
    and Gross measure 3/sqrt(5), 3.3.20, pp. 307–309. *)
Example binary_square_actual_critical_measure_values (R:realType)
    (hm:0<(1/2:R)) (hm1:(1/2:R)<1):
  let A:=@BinaryPowerCantor.value R (1/2:R) hm hm1 in
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1
    (euclidean_cantor_product A A)=(Num.sqrt (2:R))%:E /\
  @gross_measure R 2 1 (euclidean_cantor_product A A)=(3/Num.sqrt (5:R))%:E.
Proof.
move=>A.
have hDegree:0<=2 * (1/2:R) by lra.
have h:=@federer_3_3_20 R (1/2:R) hm hm1 hDegree (lexx _).
exact:h.2.2.2.2.2.2.2 erefl.
Qed.

(** Source for [binary_square_actual_supercritical_infinity]: the
    actual original exponent-three-quarters E has infinite I_infinity^1
    measure, 3.3.20, pp. 306–307. No supplied projection or mass
    premise is used. *)
Example binary_square_actual_supercritical_infinity (R:realType)
    (hm:0<(3/4:R)) (hm1:(3/4:R)<1):
  let A:=@BinaryPowerCantor.value R (3/4:R) hm hm1 in
  @integral_geometric_measure R 2 1 (erefl true) +oo (euclidean_cantor_product A A)=+oo%E.
Proof.
move=>A.
have hDegree:0<=2 * (3/4:R) by lra.
have hHalf:(1/2:R)<=3/4 by lra.
have hSuper:(1/2:R)<3/4 by lra.
have h:=@federer_3_3_20 R (3/4:R) hm hm1 hDegree hHalf.
exact:h.2.2.2.2.2.2.1 hSuper.
Qed.

(** Source for [binary_square_actual_negative_critical_direction]:
    the actual original direction (-2,1)/sqrt(5) has full
    projected length 3/sqrt(5), one of all eight directions U
    in 3.3.20, p. 307. *)
Example binary_square_actual_negative_critical_direction (R:realType)
    (hm:0<(1/2:R)) (hm1:(1/2:R)<1):
  let A:=@BinaryPowerCantor.value R (1/2:R) hm hm1 in
  lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      (-2/Num.sqrt (5:R)) * euclidean_real_plane_first p+
      (1/Num.sqrt (5:R)) * euclidean_real_plane_second p) @` euclidean_cantor_product A A)=
    (3/Num.sqrt (5:R))%:E.
Proof.
move=>A;have [f hPair]:=@BinaryPowerCantor.laws R (1/2:R) hm hm1.
have [hV [hOrder [hUnit [hRatio _]]]]:=@critical_projection_extremal_direction R.
have hRoot:0<Num.sqrt (5:R) by rewrite sqrtr_gt0 ltr0n.
have hU:(0<2/Num.sqrt (5:R)) by rewrite divr_gt0 // ltr0n.
apply:(@critical_original_all_overlap_projection_volume R 1 (-2/Num.sqrt (5:R))
  (1/Num.sqrt (5:R)) A f ltr01 hPair).
- have hNeg:((-2/Num.sqrt (5:R))^+2)=(2/Num.sqrt (5:R))^+2.
    by rewrite !expr_div_n sqrrN.
  by rewrite hNeg.
- left;rewrite mulNr normrN (ger0_norm (ltW hU)) (ger0_norm (ltW hV)).
  lra.
Qed.

(** Source for [binary_square_actual_corner_finite_stage_counterexample]:
    the actual original zero corner has diameter zero and strictly
    positive hit mass at every original finite level, qualifying the
    auxiliary finite-attainment assertion in 3.3.20, p. 308. The
    numbered measure conclusion is unchanged. *)
Example binary_square_actual_corner_finite_stage_counterexample (R:realType)
    (hm:0<(1/2:R)) (hm1:(1/2:R)<1):
  let A:=@BinaryPowerCantor.value R (1/2:R) hm hm1 in
  let z:=@euclidean_real_plane_pair R 0 0 in
  extended_metric_diameter [set z]=0%E /\
    exists G psi,is_critical_square_hit_measures G psi /\forall j,(0<psi j [set z])%E.
Proof.
move=>A z.
have [f [J [H [hJ [hTree [hA _]]]]]]:=@BinaryPowerCantor.laws R (1/2:R) hm hm1.
have [G hG]:=binary_cantor_square_levels_exist H.
have [psi [hPsi _]]:=critical_square_hit_measures_exist G.
have [hDiameter hPositive]:=@critical_square_original_singleton_qualification R _ J
  (fun _:nat=>2%N) H G psi hJ hTree hG hPsi.
split;first exact:hDiameter.
exists G,psi;by split.
Qed.
