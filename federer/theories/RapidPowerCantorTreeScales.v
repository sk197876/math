(** Federer (1969), 3.2.40, p. 276: link the
    independently specified rapid scalar schedule to actual
    interval widths and gaps of the existing Cantor tree. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  MetricDiameterReal RealPower PowerConcaveIntervalGauge
  RapidPowerCantorScalesUP RapidPowerCantorScalesLaws
  CantorSplitRadius CantorSplitRadiusUP EqualCostIntervalTreeUP
  EqualCostIntervalUniformWidths SubcriticalCantorGapBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rapid_power_cantor_tree_common_width]: supporting
    actual common widths in Federer 3.2.40, p. 276. The
    scalar sequence and the interval tree obey the same
    original split laws; uniqueness identifies their widths. *)
Lemma rapid_power_cantor_tree_common_width (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R) (J:compact_real_intervals R) H:
  0<c ->0<m ->m<1 ->is_rapid_power_cantor_scales c m n s ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  forall j S,S \in H j ->fine (@extended_metric_diameter R
    [the metricType R of real_line_metric R] (val S))=s j.
Proof.
move=>hc hm hm1 hScales hJ hTree.
have hg:=power_concave_interval_gauge hc hm hm1.
have hRoot:s 0%N=fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
  by rewrite (rapid_power_cantor_root hScales) hJ (extended_metric_diameter_segment ler01) subr0.
exact:(@equal_cost_interval_tree_uniform_widths R _ hg J n H s hTree hRoot
  (fun j=>rapid_power_cantor_split hScales j)).
Qed.

(** Source for [rapid_power_cantor_gap_bounds]: supporting scalar
    bounds on the actual consecutive child gaps in Federer
    3.2.40, p. 276. They are proved from the rapid
    recurrence and original power split, in all its stated
    subcritical and critical exponents. *)
Lemma rapid_power_cantor_gap_bounds (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R):
  0<c ->0<m ->m<=1/2 ->is_rapid_power_cantor_scales c m n s ->
  forall j,let g:=cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1 in
  s j/(n j)%:R<=g /\0<g /\s j.+1<g /\g<=s j.
Proof.
move=>hc hm hmHalf hScales j.
have hPositive:=rapid_power_cantor_width_positive hScales j.
have hj2:(2<=j.+2)%N by [].
have hCount:(2<=n j)%N:=leq_trans hj2 (rapid_power_cantor_count hScales j).
exact:(@subcritical_cantor_split_gap_bounds R c m (s j) (s j.+1) (n j)
  hc hm hmHalf hPositive hCount (rapid_power_cantor_split hScales j)).
Qed.

(** Source for [rapid_power_cantor_gaps_decrease]: supporting
    hierarchy of genuine point separations in Federer 3.2.40,
    p. 276. Every new gap is no larger than its parent
    interval width, which is less than the preceding gap. *)
Lemma rapid_power_cantor_gaps_decrease (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R):
  0<c ->0<m ->m<=1/2 ->is_rapid_power_cantor_scales c m n s ->forall j,
  cantor_split_spacing (s j.+1) (n j.+1) (s j.+2)-s j.+2<=
    cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1.
Proof.
move=>hc hm hmHalf hScales j.
have hOld:=@rapid_power_cantor_gap_bounds R c m n s hc hm hmHalf hScales j.
have hNew:=@rapid_power_cantor_gap_bounds R c m n s hc hm hmHalf hScales j.+1.
exact:le_trans hNew.2.2.2 (ltW hOld.2.2.1).
Qed.
