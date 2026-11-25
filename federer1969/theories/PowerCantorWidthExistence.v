(** Federer (1969), 3.3.21, p. 309: local existence of original widths for every original schedule. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PowerCantorWidthLawsUP RealPower CantorSplitRadiusUP CantorSplitRadius
  PowerConcaveIntervalGauge EqualCostIntervalTreeUP EqualCostIntervalUniformWidths
  RealMetricBackground MetricDiameter MetricDiameterReal CompactIntervalGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [power_cantor_original_widths_exist]: local width
    witnesses obey the original root and Phi split laws for every
    original n_j>= 2, supporting 3.3.21, p. 309. Positive scalar
    subtype recursion is only an existence proof; the witnesses are
    subsequently used through their independent public laws. *)
Theorem power_cantor_original_widths_exist (R:realType) (c m:R) (n:nat->nat):
  0<c ->0<m ->m<1 ->(forall j,(2<=n j)%N) ->
  exists w,is_power_cantor_widths c m n w.
Proof.
move=>hc hm hm1 hn.
pose P:={x:R|0<x}.
pose step (j:nat) (x:P):P:=
  exist (fun t:R=>0<t)
    (@cantor_split_radius R _ (power_concave_interval_gauge hc hm hm1) (proj1_sig x) (n j)
      (proj2_sig x) (hn j))
    (cantor_split_radius_bounds (@cantor_split_radius_specification R _
      (power_concave_interval_gauge hc hm hm1) (proj1_sig x) (n j) (proj2_sig x) (hn j))).1.
pose values:=fix values (j:nat):P:=if j is k.+1 then step k (values k) else exist (fun t:R=>0<t) 1 ltr01.
pose w j:=proj1_sig (values j).
exists w;constructor;first by [].
- move=>j;exact:proj2_sig (values j).
- move=>j;exact:cantor_split_radius_specification.
Qed.

(** Source for [power_cantor_original_widths_identify]: every
    actual original interval at level j has the common width w_j,
    supporting the actual ball separation for 3.3.21, p. 309.
    The original recursion, abstract widths and split uniqueness prove it. *)
Theorem power_cantor_original_widths_identify (R:realType) (c m:R)
    (J:compact_real_intervals R) n H w:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_power_cantor_widths c m n w ->forall j S,S \in H j ->
  fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=w j.
Proof.
move=>hc hm hm1 hJ hTree hWidth.
apply:(@equal_cost_interval_tree_uniform_widths R _ (power_concave_interval_gauge hc hm hm1)
  J n H w hTree).
- by rewrite (power_cantor_width_root hWidth) hJ (extended_metric_diameter_segment ler01) subr0.
- exact:power_cantor_width_split hWidth.
Qed.
