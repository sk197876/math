(** Federer (1969), 3.3.20, pp. 306–308: actual equal-side square coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorLevelWidths MetricDiameter MetricDiameterReal RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_original_square_coordinates]: every actual
    original level square has the printed common side (2^(-1/m))^j,
    3.3.20, pp. 306–308. Only its lower corner is selected locally;
    the original compact intervals and endpoints remain unchanged. *)
Theorem binary_cantor_original_square_coordinates (R:realType) (c m:R)
    (J S T:compact_real_intervals R) H j:
  0<c ->0<m ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  S \in H j ->T \in H j ->
  exists a b:R,val S=(`[a,a+(real_power 2 (-m^-1))^+j]:set (real_line_metric R)) /\
    val T=(`[b,b+(real_power 2 (-m^-1))^+j]:set (real_line_metric R)).
Proof.
move=>hc hm hJ hTree hS hT.
have hWidth U (hU:U \in H j):fine (@extended_metric_diameter R
    [the metricType R of real_line_metric R] (val U))=(real_power 2 (-m^-1))^+j.
  exact:(@binary_cantor_level_width R c m J H hc hm hJ hTree j U hU).
have [a [u [hau hSV]]]:=set_valP S.
have [b [v [hbv hTV]]]:=set_valP T.
have hSW:=hWidth S hS;rewrite hSV (extended_metric_diameter_segment hau) /= in hSW.
have hTW:=hWidth T hT;rewrite hTV (extended_metric_diameter_segment hbv) /= in hTW.
have hU:u=a+(real_power 2 (-m^-1))^+j by lra.
have hV:v=b+(real_power 2 (-m^-1))^+j by lra.
exists a,b;by rewrite -hU -hV.
Qed.
