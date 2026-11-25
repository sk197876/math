(** Federer (1969), 3.2.40, p. 276, using
    the actual Cantor levels from 2.10.28, p. 193:
    every finite level has a member. *)
From mathcomp Require Import all_boot all_order all_algebra finmap
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge
  EqualCostIntervalTreeUP EqualCostIntervalFamilyUP SpecialIntervalRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_tree_level_nonempty]: supporting
    selection of a true positive level width in Federer
    3.2.40, p. 276. The original root is a singleton;
    every parent has a nonempty actual Phi child family.
    No replacement scalar width or limit point is selected. *)
Lemma equal_cost_interval_tree_level_nonempty (R:realType) (h:R->R)
    (J:compact_real_intervals R) n H:
  is_equal_cost_interval_tree h J n H ->forall j,exists S,S \in H j.
Proof.
move=>hTree; elim=>[|j [S hS]].
- exists J; by rewrite (equal_cost_tree_root hTree) in_fset1.
- have [K [hK hNext]]:=equal_cost_tree_step hTree j.
  have [T hT]:=equal_cost_interval_family_nonempty (hK S hS).
  exists T; rewrite hNext.
  apply:(@special_interval_refinement_membership R (H j) K T).2.
  by exists S.
Qed.
