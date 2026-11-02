(** Public iteration interface for Federer (1969), 2.8.12, p. 149. The two
    functions are used only through the abstract repeated-selection laws,
    never through the private recursion. Source context and indexing:
    RadiusSelectionIterationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP RadiusSelectionIterationUP
  RadiusSelectionIterationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radius_selection_iteration]: the eligible and
    selected sequences in Federer 2.8.12, p. 149, selected
    through the sealed specification. *)
Definition radius_selection_iteration (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) (ht : 1 < tau) (hm : 0 < mu)
    (hQ : is_bounded_positive_radius_family mu Q) :=
  @RadiusSelectionIteration.value R X tau mu Q ht hm hQ.

(** Source for [radius_selection_iteration_specification]: the
    chosen functions satisfy the three iteration laws from the
    proof of Federer 2.8.12, p. 149. *)
Lemma radius_selection_iteration_specification (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) (ht : 1 < tau) (hm : 0 < mu)
    (hQ : is_bounded_positive_radius_family mu Q) :
  is_radius_selection_iteration tau Q
    (@radius_selection_iteration R X tau mu Q ht hm hQ).1
    (@radius_selection_iteration R X tau mu Q ht hm hQ).2.
Proof. exact: RadiusSelectionIteration.laws. Qed.
