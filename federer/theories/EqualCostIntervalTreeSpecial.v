(** Federer (1969), 2.10.28, p. 193: the recursively constructed equal-cost
    levels satisfy the hypotheses of (3), including mesh tending to zero.
    The single-root condition is Federer's own correction: erratum p. 4,
    book p. 192 line 4. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MetricDiameter CompactIntervalGauge ConcaveIntervalGaugeUP
  EqualCostIntervalFamilyUP EqualCostIntervalSpecial EqualCostIntervalTreeUP EqualCostIntervalTreeLaws
  SpecialIntervalFamilyUP SpecialIntervalRefinement SpecialIntervalRefinementRestriction SequencePowerBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [equal_cost_interval_tree_special]: supporting
    application of (3) to the Phi recursion
    in 2.10.28, p. 193. Every stated
    special-tree hypothesis is derived; the
    recursive interface assumes none of the
    desired measure or shrinking-mesh conclusions. *)
Theorem equal_cost_interval_tree_special (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) J n H
    (ht : is_equal_cost_interval_tree h J n H) : is_special_interval_tree h H.
Proof.
have hlevel := @equal_cost_tree_level_special R h hg J n H ht.
constructor.
- exists J; exact: equal_cost_tree_root ht.
- move=> j S T hS hT hne.
  exact: (@special_intervals_disjoint R h J (H j) (hlevel j) S T hS hT hne).
- move=> j U hU; have [K [hK he]] := equal_cost_tree_step ht j.
  rewrite he in hU.
  have [S [hS hUS]] := (@special_interval_refinement_membership R (H j) K U).1 hU.
  exists S; split=> //.
  exact: (@special_interval_subsets R h S (K S)
    (@federer_2_10_28_4_special R h hg S (n j) (K S) (hK S hS)) U hUS).
- move=> j S hS; have [K [hK he]] := equal_cost_tree_step ht j.
  have hKS T hT := @federer_2_10_28_4_special R h hg T (n j) (K T) (hK T hT).
  rewrite he (@special_interval_refinement_restriction R h J (H j) K (hlevel j) hKS S hS).
  exact: hKS S hS.
- move=> e he.
  pose d := fine (@extended_metric_diameter R [the metricType R of real_line_metric R] (val J)).
  have hJmem : J \in H 0%N by rewrite (equal_cost_tree_root ht) in_fset1.
  have hd : 0<d := @equal_cost_tree_member_positive R h J n H ht 0%N J hJmem.
  have hediv : 0<e/d by rewrite divr_gt0.
  have [N hN] := @sequence_inverse_power_small R (e/d) hediv.
  have hsmall : d*(2^-1)^+N<e by move: hN; rewrite ltr_pdivlMr // mulrC.
  exists N=> j hNj S hS.
  have hhalf0 : (0<=2^-1 :> R) by rewrite invr_ge0 ler0n.
  have hhalf1 : (2^-1<=1 :> R) by rewrite invf_le1 ?ltr0n // ler1n.
  have hpow : (2^-1)^+j<=(2^-1)^+N :> R.
    apply: ler_wiXn2l; [exact hhalf0 | exact hhalf1 | exact hNj].
  have hmul := ler_wpM2l (ltW hd) hpow.
  exact: le_trans (@equal_cost_tree_mesh_bound R h J n H ht j S hS) (le_trans hmul (ltW hsmall)).
Qed.
