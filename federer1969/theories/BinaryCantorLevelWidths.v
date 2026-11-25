(** Federer (1969), 3.3.20, pp. 306–308:
    exact original binary interval lengths at every level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter MetricDiameterReal
  EqualCostIntervalTreeUP EqualCostIntervalTreeLaws EqualCostIntervalChildLaws
  SpecialIntervalRefinement PowerCantorSplit RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_level_width]: the original
    interval side at level j equals (2^(-1/m))^j,
    supporting the actual square levels of 3.3.20,
    pp. 306–308. It follows from the original
    equal-cost child laws, not from an extra width
    recurrence or a replacement interval construction. *)
Theorem binary_cantor_level_width (R:realType) (c m:R)
    (J:compact_real_intervals R) H:
  0<c ->0<m ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J (fun _:nat=>2%N) H ->
  forall j S,S \in H j ->
    fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S))=
      (real_power 2 (-m^-1))^+j.
Proof.
move=>hc hm hJ hTree;elim=>[S|j ih S] hS.
- move:hS;rewrite (equal_cost_tree_root hTree) in_fset1=>/eqP->.
  by rewrite hJ (extended_metric_diameter_segment (@ler01 R)) subr0 expr0.
- have [K [hK hStep]]:=equal_cost_tree_step hTree j.
  rewrite hStep in hS.
  have [P [hP hChild]]:=(@special_interval_refinement_membership R (H j) K S).1 hS.
  have hSplit:=@equal_cost_interval_child_split_laws R _ P 2 (K P) S (hK P hP) hChild.
  have hParent:=@equal_cost_tree_member_positive R _ J (fun _:nat=>2%N) H hTree j P hP.
  have hExact:=@power_cantor_split_length R c m
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val P)))
    (fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val S)))
    2 hc hm hParent (leqnn 2) hSplit.
  by rewrite (ih P hP) exprSr in hExact *.
Qed.
