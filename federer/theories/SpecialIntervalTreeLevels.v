(** Federer (1969), 2.10.28(3), p. 192: the corrected single-root tree
    consists at every level of a family special for the same root. Its later
    intervals have unique ancestors in earlier levels and are contained in
    or disjoint from any fixed earlier member. Use Federer's own correction,
    erratum p. 4, book p. 192 line 4, for the initial singleton. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP
  SpecialIntervalFamilyUP SpecialIntervalFamilyBasic SpecialIntervalRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [special_interval_tree_step_refinement]: supporting
    exact union of the child subfamilies in
    2.10.28(3), p. 192. Every interval
    at the next level has a parent; each
    restricted child subfamily already lies in
    that level. *)
Lemma special_interval_tree_step_refinement (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H) j :
  special_interval_refinement (H j) (fun S=>special_interval_restriction (H j.+1) (val S))=H j.+1.
Proof.
apply/fsetP=> U; apply/idP/idP.
- move=> /special_interval_refinement_membership[S [hS hU]].
  exact: ((special_interval_restriction_membership _ _ _).1 hU).1.
- move=> hU; have [S [hS hsub]] := @special_tree_refinement R h H ht j U hU.
  apply/special_interval_refinement_membership; exists S; split=> //.
  apply/special_interval_restriction_membership; by split.
Qed.

(** Source for [special_interval_tree_level_special]: supporting induction
    in 2.10.28(3), p. 192, from the corrected singleton H_0. *)
Theorem special_interval_tree_level_special (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (H : nat -> {fset compact_real_intervals R})
    (ht : is_special_interval_tree h H) (J : compact_real_intervals R) :
  H 0%N=[fset J] -> forall j, is_special_interval_family h J (H j).
Proof.
move=> hroot; elim=> [|j ih].
- rewrite hroot; exact (@special_interval_singleton R h hg J).
- have hh := @federer_2_10_28_2 R h hg J (H j)
    (fun S=>special_interval_restriction (H j.+1) (val S)) ih
    (fun S hS=>@special_tree_children R h H ht j S hS).
  by rewrite (special_interval_tree_step_refinement ht) in hh.
Qed.

(** Source for [special_interval_tree_ancestor]: supporting
    repeated parent containment in 2.10.28(3),
    p. 192. Every interval at level j+n
    lies in some interval at level j,
    including n=0. *)
Lemma special_interval_tree_ancestor (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H) j n U :
  U \in H (j+n)%N -> exists S, S \in H j /\ val U `<=` val S.
Proof.
elim: n U=> [U|n ih U]; first by rewrite addn0=> hU; exists U; split.
rewrite addnS=> hU.
have [V [hV hUV]] := @special_tree_refinement R h H ht (j+n)%N U hU.
have [S [hS hVS]] := ih V hV.
exists S; split=> // x hx; exact: hVS x (hUV x hx).
Qed.

(** Source for [special_interval_tree_level_relation]: supporting
    fact that a later member lies in or
    is disjoint from a fixed earlier member,
    used in the lower mass bound of
    2.10.28(3), p. 192. Full closed-set
    disjointness preserves endpoint cases. *)
Lemma special_interval_tree_level_relation (R : realType) (h : R -> R)
    (H : nat -> {fset compact_real_intervals R}) (ht : is_special_interval_tree h H) j n S U :
  S \in H j -> U \in H (j+n)%N -> val U `<=` val S \/ val U `&` val S=set0.
Proof.
move=> hS hU; have [V [hV hUV]] := @special_interval_tree_ancestor R h H ht j n U hU.
case: (eqVneq V S)=> [he|hne]; first by left; rewrite -he.
right; apply/seteqP; split=> [x [hxU hxS]|x []].
have he := @special_tree_disjoint R h H ht j V S hV hS hne.
have hmem : (val V `&` val S) x by split; [exact: hUV x hxU | exact hxS].
by rewrite he in hmem.
Qed.
