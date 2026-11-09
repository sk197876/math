(** Federer (1969), 3.3.20, pp. 307–308:
    original descendants satisfy the original recursion at their own parent. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  EqualCostIntervalTreeUP EqualCostIntervalTreeSpecial EqualCostIntervalTreeLinks
  SpecialIntervalFamilyUP SpecialIntervalFamilyBasic SpecialIntervalRefinement SpecialIntervalDescendants.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.

(** Source for [equal_cost_interval_original_descendants]:
    supporting original-parent reduction in 3.3.20,
    pp. 307–308. Restricting every actual later
    level to an original interval gives the original
    Phi recursion starting at that interval, with
    the shifted original subdivision schedule. No
    new recursive construction is substituted. *)
Theorem equal_cost_interval_original_descendants (R:realType) (h:R->R)
    (hGauge:is_concave_interval_gauge h) (J:compact_real_intervals R) n H j S:
  is_equal_cost_interval_tree h J n H ->S \in H j ->
  is_equal_cost_interval_tree h S (fun k=>n (j+k)%N)
    (fun k=>special_interval_restriction (H (j+k)%N) (val S)).
Proof.
move=>hTree hS.
have hSpecial:=@equal_cost_interval_tree_special R h hGauge J n H hTree.
constructor.
- by rewrite addn0 (special_interval_same_level_restriction hSpecial hS).
- move=>k.
  exists (fun U=>special_interval_restriction (H (j+k).+1%N) (val U));split.
  + move=>U /special_interval_restriction_membership[hU _].
    exact:(@equal_cost_tree_restricted_children_phi R h hGauge J n H hTree (j+k)%N U hU).
  + rewrite addnS;exact:esym (@special_interval_restricted_step R h H hSpecial j k S hS).
Qed.
