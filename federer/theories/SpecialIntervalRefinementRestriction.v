(** Federer (1969), 2.10.28(2)–(3), p. 192, and recursive application p.
    193: restricting a refinement to a parent recovers exactly its child
    family. This supporting fact uses the nonempty closed interval sets and
    disjoint parents; it is not a new book hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  SpecialIntervalFamilyBasic SpecialIntervalRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.

(** Source for [special_interval_refinement_restriction]: supporting
    identity between the children attached to S
    and the next level's members contained in S,
    used in 2.10.28(3), p. 192. Whole
    closed intervals are used, including endpoints. *)
Theorem special_interval_refinement_restriction (R : realType) (h : R -> R)
    (J : compact_real_intervals R) H (K : compact_real_intervals R -> {fset compact_real_intervals R}) :
  is_special_interval_family h J H ->
  (forall S, S \in H -> is_special_interval_family h S (K S)) ->
  forall S, S \in H ->
    special_interval_restriction (special_interval_refinement H K) (val S)=K S.
Proof.
move=> hH hK S hS; apply/fsetP=> U; apply/idP/idP.
- move=> /special_interval_restriction_membership[/special_interval_refinement_membership[T [hT hU]] hUS].
  case: (eqVneq T S)=> [he|hne]; first by rewrite -he.
  have [x hx] := compact_real_interval_nonempty (set_valP U).
  have hUT := @special_interval_subsets R h T (K T) (hK T hT) U hU.
  have hmem : (val T `&` val S) x by split; [exact: hUT x hx | exact: hUS x hx].
  by rewrite (@special_intervals_disjoint R h J H hH T S hT hS hne) in hmem.
- move=> hU; apply/special_interval_restriction_membership; split.
  + apply/special_interval_refinement_membership; exists S; by split.
  + exact: (@special_interval_subsets R h S (K S) (hK S hS) U hU).
Qed.
