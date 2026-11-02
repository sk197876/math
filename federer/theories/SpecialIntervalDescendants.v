(** Federer (1969), 2.10.28(3), p. 192: the descendants at any later level
    inside a fixed member form a family special for that member. This
    supplies the exact cost sums in the lower mass estimate. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  SpecialIntervalFamilyUP SpecialIntervalFamilyBasic SpecialIntervalRefinement SpecialIntervalTreeLevels.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [special_interval_same_level_restriction]:
    supporting singleton initial family for the
    descendants of T in 2.10.28(3), p. 192.
    Nonempty disjoint members at the same level
    cannot be proper subsets of each other. *)
Lemma special_interval_same_level_restriction (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H) j T :
  T \in H j -> special_interval_restriction (H j) (val T)=[fset T].
Proof.
move=> hT; apply/fsetP=> U; apply/idP/idP.
- move=> /special_interval_restriction_membership[hU hsub].
  case: (eqVneq U T)=> [he|hne]; first by rewrite he inE eqxx.
  have [x hx] := compact_real_interval_nonempty (set_valP U).
  have hmem : (val U `&` val T) x by split=> //; exact: hsub x hx.
  by rewrite (@special_tree_disjoint R h H ht j U T hU hT hne) in hmem.
- move=> /fset1P ->; apply/special_interval_restriction_membership; by split.
Qed.

(** Source for [special_interval_restricted_step]: supporting refinement
    identity for the restricted later families H'_k in 2.10.28(3), p. 192 A
    child inside T has a parent inside T, since other parents are disjoint
    from T. *)
Lemma special_interval_restricted_step (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H) j n T :
  T \in H j ->
  special_interval_refinement (special_interval_restriction (H (j+n)%N) (val T))
    (fun S=>special_interval_restriction (H (j+n).+1%N) (val S))=
    special_interval_restriction (H (j+n).+1%N) (val T).
Proof.
move=> hT; apply/fsetP=> U; apply/idP/idP.
- move=> /special_interval_refinement_membership[S [hS hU]].
  have [hSold hST] := (special_interval_restriction_membership _ _ _).1 hS.
  have [hUnext hUS] := (special_interval_restriction_membership _ _ _).1 hU.
  apply/special_interval_restriction_membership; split=> // x hx; exact: hST x (hUS x hx).
- move=> /special_interval_restriction_membership[hU hUT].
  have [S [hS hUS]] := @special_tree_refinement R h H ht (j+n)%N U hU.
  have hST : val S `<=` val T.
    case: (@special_interval_tree_level_relation R h H ht j n T S hT hS)=> // he.
    have [x hx] := compact_real_interval_nonempty (set_valP U).
    have hmem : (val S `&` val T) x by split; [exact: hUS x hx | exact: hUT x hx].
    by rewrite he in hmem.
  apply/special_interval_refinement_membership; exists S; split;
    apply/special_interval_restriction_membership; by split.
Qed.

(** Source for [special_interval_descendants_special]: supporting
    specialness of H'_k for T in the lower bound proof of 2.10.28(3), p. 192
    Iterate (2) starting with {T}; retain empty zero-cost child families and
    singleton intervals rather than assuming positive diameter. *)
Theorem special_interval_descendants_special (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (H : nat -> {fset compact_real_intervals R})
    (ht : is_special_interval_tree h H) j T :
  T \in H j -> forall n,
  is_special_interval_family h T (special_interval_restriction (H (j+n)%N) (val T)).
Proof.
move=> hT; elim=> [|n ih].
- rewrite addn0 (special_interval_same_level_restriction ht hT).
  exact: (@special_interval_singleton R h hg T).
- have hchild S (hS : S \in special_interval_restriction (H (j+n)%N) (val T)) :
      is_special_interval_family h S (special_interval_restriction (H (j+n).+1%N) (val S)).
    have hSold := ((special_interval_restriction_membership _ _ _).1 hS).1.
    exact: (@special_tree_children R h H ht (j+n)%N S hSold).
  have hh := @federer_2_10_28_2 R h hg T
    (special_interval_restriction (H (j+n)%N) (val T))
    (fun S=>special_interval_restriction (H (j+n).+1%N) (val S)) ih hchild.
  rewrite (@special_interval_restricted_step R h H ht j n T hT) in hh.
  by rewrite addnS.
Qed.
