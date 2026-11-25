(** Federer (1969), 3.2.40, p. 276: the
    actual positive packing radii tend to zero, through
    the original compact interval-tree mesh laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  RealPower PowerConcaveIntervalGauge RapidPowerCantorScalesUP
  RapidPowerCantorTreeScales EqualCostIntervalTreeUP EqualCostIntervalTreeSpecial
  EqualCostIntervalTreeNonempty SpecialIntervalFamilyUP CantorSplitRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rapid_cantor_gap_radii_eventually_small]: supporting
    upper-content divergence in Federer 3.2.40, p. 276.
    Every packing radius is a positive quarter of its actual
    child gap; that gap is bounded by the parent width.
    Actual nonempty interval levels and their earlier uniform
    mesh therefore make all later radii arbitrarily small. *)
Lemma rapid_cantor_gap_radii_eventually_small (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R) (J:compact_real_intervals R)
    (H:nat->{fset compact_real_intervals R}) (d:R):
  0<c ->0<m ->m<=1/2 ->is_rapid_power_cantor_scales c m n s ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->0<d ->
  exists N:nat,forall j,(N<=j)%N ->
    0<(cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1)/4<d.
Proof.
move=>hc hm hmHalf hScales hJ hTree hd.
have hm1:m<1 by lra.
have hg:=power_concave_interval_gauge hc hm hm1.
have hSpecial:=@equal_cost_interval_tree_special R _ hg J n H hTree.
have [N hMesh]:=@special_tree_mesh R _ H hSpecial d hd.
have hWidth:=@rapid_power_cantor_tree_common_width R c m n s J H hc hm hm1 hScales hJ hTree.
exists N=>j hNj.
have [S hS]:=equal_cost_interval_tree_level_nonempty hTree j.
have hSmall:=hMesh j hNj S hS.
rewrite (hWidth j S hS) in hSmall.
have hGap:=@rapid_power_cantor_gap_bounds R c m n s hc hm hmHalf hScales j.
have hPositive:=hGap.2.1.
have hBound:=le_trans hGap.2.2.2 hSmall.
apply/andP; split; first by rewrite divr_gt0 // ltr0n.
lra.
Qed.
