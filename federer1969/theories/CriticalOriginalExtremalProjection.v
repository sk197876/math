(** Federer (1969), 3.3.20, p. 307: the actual extremal critical projection. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground PowerCantorPairUP BinaryCantorSquareLevelsUP
  BinaryCantorFullIntervalProjection CriticalCantorRatio CriticalProjectionScalarBound
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct LebesgueScalarMeasure RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_extremal_projection]: the original
    slope-one-half unit direction gives a full projected interval of
    length 3/sqrt(5), supporting the Gross-measure lower bound in
    3.3.20, p. 307. The actual original compact-limit projection
    theorem proves the image; the source is not replaced and actual
    Lebesgue interval length proves its mass. *)
Theorem critical_original_extremal_projection (R:realType) (c:R)
    (A:set (real_line_metric R)) (f:R->R):
  0<c ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  let u:=(2:R)/Num.sqrt 5 in let v:=(1:R)/Num.sqrt 5 in
  let P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p in
  P @` euclidean_cantor_product A A=(`[0,3/Num.sqrt 5]:set R) /\
    lebesgue_scalar_measure (P @` euclidean_cantor_product A A)=(3/Num.sqrt (5:R))%:E.
Proof.
move=>hc [J [H [hJ [hTree [hA _]]]]] u v P.
have [hv [hvu [hUnit [hRatio _]]]]:=@critical_projection_extremal_direction R.
change (is_true (0<v)) in hv.
change (is_true (v<=u)) in hvu.
change (v=u/2) in hRatio.
have hu:0<u:=lt_le_trans hv hvu.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have [G hG]:=binary_cantor_square_levels_exist H.
have hMiddle:(1-2 * real_power 2 (-((1/2:R))^-1)) * u<=v.
  rewrite critical_cantor_binary_ratio;by nra.
have hSide:(1-2 * real_power 2 (-((1/2:R))^-1)) * v<=real_power 2 (-((1/2:R))^-1) * u.
  rewrite critical_cantor_binary_ratio;by nra.
have hFull:=@binary_original_cantor_square_full_interval_projection R c (1/2:R) u v J H G A
  hc hm hm1 hu (ltW hv) hvu hJ hTree hA hG hMiddle hSide.
have hRoot:0<Num.sqrt (5:R) by rewrite sqrtr_gt0 ltr0n.
have hNZ:Num.sqrt (5:R)!=0 by rewrite gt_eqF.
have hEnd:u+v=3/Num.sqrt (5:R) by rewrite /u /v;field.
change (P @` euclidean_cantor_product A A=(`[0,u+v]:set R)) in hFull.
rewrite hEnd in hFull;split;first exact:hFull.
have hPositive:0<(3/Num.sqrt (5:R)) by rewrite divr_gt0 // ltr0n.
by rewrite hFull (lebesgue_scalar_segment (ltW hPositive)) subr0.
Qed.
