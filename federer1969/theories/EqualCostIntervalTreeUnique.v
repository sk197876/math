(** Federer (1969), 3.3.20, pp. 307–308:
    the original interval recursion determines all its levels uniquely. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  EqualCostIntervalFamilyUP EqualCostIntervalTreeUP SpecialIntervalRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope fset_scope.

(** Source for [equal_cost_interval_tree_unique]: supporting
    identification of the ACTUAL original levels under
    the similarities in 3.3.20, pp. 307–308.
    Equal root and original Phi laws determine every
    level. Auxiliary children outside the current
    parent family have no role and are not compared. *)
Theorem equal_cost_interval_tree_unique (R:realType) (h:R->R)
    (hGauge:is_concave_interval_gauge h) J n H K:
  is_equal_cost_interval_tree h J n H ->is_equal_cost_interval_tree h J n K ->H=K.
Proof.
move=>hH hK;apply:funext;elim=>[|j ih].
- by rewrite (equal_cost_tree_root hH) (equal_cost_tree_root hK).
- have [A [hA hNextH]]:=equal_cost_tree_step hH j.
  have [B [hB hNextK]]:=equal_cost_tree_step hK j.
  have hChildren P:P \in H j ->A P=B P.
    move=>hP;have hPK:P \in K j by rewrite -ih.
    exact:(@equal_cost_interval_family_unique R h hGauge P (n j) (A P) (B P) (hA P hP) (hB P hPK)).
  rewrite hNextH hNextK;apply/fsetP=>S;apply/idP/idP.
  + move=>/special_interval_refinement_membership[P [hP hS]].
    apply/special_interval_refinement_membership;exists P;split;first by rewrite -ih.
    by rewrite -(hChildren P hP).
  + move=>/special_interval_refinement_membership[P [hP hS]].
    have hPH:P \in H j by rewrite ih.
    apply/special_interval_refinement_membership;exists P;split=>//.
    by rewrite hChildren.
Qed.
