(** Federer (1969), 2.10.28, Cantor construction, p. 193: begin at one
    nondegenerate interval and refine its members by Phi(S,n_j). The laws
    specify the levels before choosing a recursive implementation. The
    book's [0,1] case is a consequence of this more general parent-interval
    specification. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalFamilyUP
  SpecialIntervalRefinement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope fset_scope.

(** Source for [is_equal_cost_interval_tree]: direct
    H_0={J} and H_(j+1)=union Phi(S,n_(j+1))
    in 2.10.28, p. 193. The schedule
    n uses zero-based indices, so n(j) is
    the book's n_(j+1). The child families
    are specified by their laws; no mesh or
    measure conclusion is a defining assumption. *)
Record is_equal_cost_interval_tree (R : realType) (h : R -> R)
    (J : compact_real_intervals R) (n : nat -> nat)
    (H : nat -> {fset compact_real_intervals R}) : Prop := {
  (** Source for [equal_cost_tree_root]: direct
      singleton initial family on p. 193,
      consistent with the correction to (3),
      erratum p. 4, book p. 192 line 4. *)
  equal_cost_tree_root : H 0%N=[fset J];
  (** Source for [equal_cost_tree_step]: direct
      union of the specified Phi families
      in 2.10.28, p. 193. Values of
      K outside the current family have no role. *)
  equal_cost_tree_step : forall j, exists K : compact_real_intervals R -> {fset compact_real_intervals R},
    (forall S, S \in H j -> is_equal_cost_interval_family h S (n j) (K S)) /\
    H j.+1=special_interval_refinement (H j) K
}.
