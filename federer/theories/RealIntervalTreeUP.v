(** Federer (1969), 2.2.9, p. 65: in the case X=R, choose all non-root U(s)
    to be intervals so that the image has countable complement. This record
    extends the general open-tree laws without requiring disjoint closures
    of siblings. Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals
  OpenEmbeddingTreeUP OpenEmbeddingCountableComplement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_real_interval_embedding_tree]: abstract
    interval-tree specification for the special case in Federer
    2.2.9, p. 65: all general open-tree laws hold, each
    non-root node is a nonempty real interval, and each parent
    loses at most countably many points at the next level. *)
Record is_real_interval_embedding_tree (R : realType)
    (U : seq nat -> set (real_line_metric R)) : Prop := {
  real_interval_tree_open_laws : is_open_embedding_tree U;
  real_interval_tree_intervals : forall s, s != [::] ->
    exists a b, a < b /\ U s = real_open_interval a b;
  real_interval_tree_countable_loss : forall s, countable (open_embedding_child_loss U s)
}.
