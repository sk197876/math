(** Federer (1969), 3.2.40, p. 276: specify and
    prove local selection of actual limit-set points from
    each positive-cost interval of a finite Cantor level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge RealPower
  PowerConcaveIntervalGauge EqualCostIntervalTreeUP EqualCostIntervalTreeLaws
  EqualCostIntervalTreeSpecial SpecialIntervalFamilyUP SpecialIntervalTreeTopology
  MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_interval_level_point_selection]: supporting independent
    point-selection laws for Federer 3.2.40, p. 276. Each
    selected point belongs both to the original limit set and
    to its actual ordinal-indexed level interval. Separation,
    tube volume and contents are not defining assumptions. *)
Definition is_interval_level_point_selection (R:realType)
    (J:compact_real_intervals R) (F:{fset compact_real_intervals R})
    (A:set (real_line_metric R))
    (v:'I_(size (F:seq (compact_real_intervals R)))->real_line_metric R):Prop:=
  forall i,A (v i) /\val (nth J F i) (v i).

(** Source for [power_cantor_level_point_selection_exists]: supporting
    actual finite point packing for Federer 3.2.40, p. 276.
    Positive level cost and the already proved nested compact
    interval argument give a true point of the original limit
    in each member. Choice stays local to this existence proof;
    no endpoint persistence or global selected map is assumed. *)
Lemma power_cantor_level_point_selection_exists (R:realType) (c m:R)
    (J:compact_real_intervals R) n H (A:set (real_line_metric R)) j:
  0<c ->0<m ->m<1 ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  is_special_interval_tree_limit H A ->
  exists v,@is_interval_level_point_selection R J (H j) A v.
Proof.
move=>hc hm hm1 hTree hA.
have hg:=power_concave_interval_gauge hc hm hm1.
have hSpecial:=@equal_cost_interval_tree_special R _ hg J n H hTree.
have hExist (i:'I_(size (H j:seq (compact_real_intervals R)))):
    exists x:real_line_metric R,A x /\val (nth J (H j) i) x.
  have hMember:nth J (H j) i \in H j:=mem_nth J (ltn_ord i).
  have hPositive:=@equal_cost_tree_member_positive R _ J n H hTree j _ hMember.
  have hCost:0<concave_interval_cost (fun t=>c*real_power t m) (val (nth J (H j) i)).
    rewrite /concave_interval_cost.
    exact:(mulr_gt0 hc (@real_power_strictly_positive R _ m hPositive)).
  exact:(@positive_interval_member_meets_limit R _ hg H hSpecial A hA j _ hMember hCost).
have [v hV]:=choice hExist.
by exists v.
Qed.
