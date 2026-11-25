(** Federer (1969), 3.3.20, p. 307: exact critical volume on every direction in U. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP BinaryCantorAllDirectionProjection
  CriticalAllDirectionProjectionLocus CriticalCantorRatio PowerCantorPairUP
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct
  LebesgueScalarMeasure ScalarAffineLebesgue RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_all_overlap_projection_volume]:
    all eight critical unit directions in the printed U have actual
    original projection length 3/sqrt(5), 3.3.20, p. 307. The
    complete signed original interval image, actual scalar translation
    invariance and the exact unit-direction norm identity prove it. *)
Theorem critical_original_all_overlap_projection_volume (R:realType) (c u v:R)
    (A:set (real_line_metric R)) (f:R->R):
  0<c ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  u^+2+v^+2= 1 ->(`|u|= 2 * `|v| \/ `|v|= 2 * `|u|) ->
  lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
      euclidean_cantor_product A A)=(3/Num.sqrt (5:R))%:E.
Proof.
move=>hc [J [H [hJ [hTree [hA _]]]]] hUnit hLocus.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have hU:binary_full_projection_direction (1/4:R) u v
  :=(critical_binary_all_direction_projection_locus u v).2 hLocus.
have [G hG]:=binary_cantor_square_levels_exist H.
have hULambda:binary_full_projection_direction (real_power 2 (-((1/2:R)^-1))) u v
  by rewrite critical_cantor_binary_ratio -div1r;exact:hU.
have hImage:=(@binary_original_all_direction_full_projection R c (1/2:R) u v J H G A
  hc hm hm1 hUnit hJ hTree hA hG).2 hULambda.
rewrite hImage.
have hShift:(fun t:R=>t+(u-`|u|+v-`|v|)/2)=
    (fun t:R=>1 * t+(u-`|u|+v-`|v|)/2) by apply:funext=>t;ring.
rewrite hShift scalar_affine_lebesgue_image ?oner_eq0 // normr1 mul1e.
have hNonnegative:0<=`|u|+ `|v| :=addr_ge0 (normr_ge0 u) (normr_ge0 v).
by rewrite (lebesgue_scalar_segment hNonnegative) subr0
  (critical_binary_overlap_direction_length hUnit hU).
Qed.
