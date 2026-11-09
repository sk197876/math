(** Federer (1969), 3.3.20, pp. 307–308:
    the actual descendant limit is the original Cantor set restricted to its parent. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  SpecialIntervalFamilyBasic SpecialIntervalRefinement SpecialIntervalTreeLevels
  SpecialIntervalTreeTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [special_interval_original_descendant_limit]:
    supporting ACTUAL original piece identity in
    3.3.20, pp. 307–308. The limit
    of the actual later levels inside S is
    exactly A intersect S. Original disjoint parent
    laws identify every descendant, and level
    monotonicity recovers all earlier levels. *)
Theorem special_interval_original_descendant_limit (R:realType) (h:R->R)
    (H:nat->{fset compact_real_intervals R}) (A:set (real_line_metric R)) j S:
  is_special_interval_tree h H ->is_special_interval_tree_limit H A ->S \in H j ->
  is_special_interval_tree_limit
    (fun k=>special_interval_restriction (H (j+k)%N) (val S)) (A `&` val S).
Proof.
move=>hTree hA hS y;split.
- move=>[hyA hyS] k.
  have [U [hU hyU]]:=(hA y).1 hyA (j+k)%N.
  have hSubset:val U `<=` val S.
    case:(@special_interval_tree_level_relation R h H hTree j k S U hS hU)=>// hDisjoint.
    have hPoint:(val U `&` val S) y by split.
    by rewrite hDisjoint in hPoint.
  exists U;split=>//;apply/special_interval_restriction_membership;by split.
- move=>hLevels;split.
  + apply:(hA y).2=>k.
    have [U [/special_interval_restriction_membership[hU _] hyU]]:=hLevels k.
    have hIndex:(k<=j+k)%N:=leq_addl j k.
    have hLater:(\bigcup_(V in [set` H (j+k)%N]) val V) y by exists U.
    have [V hV hyV]:=@special_interval_level_union_antitone R h H hTree k (j+k)%N hIndex y hLater.
    exists V;by split.
  + have [U [/special_interval_restriction_membership[_ hUS] hyU]]:=hLevels 0%N.
    exact:hUS y hyU.
Qed.
