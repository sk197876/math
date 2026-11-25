(** Opaque witness for the repeated selections in Federer (1969), 2.8.12, p.
    149. The recursion is hidden by module ascription; users receive only
    the remainder and selection functions and their abstract laws. Source
    context: RadiusSelectionIterationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP RadiusSelectionIterationUP
  RadiusSelectionIterationConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module Type RadiusSelectionIterationSignature.
(** Source for [value]: the repeated-selection functions in
    Federer 2.8.12, p. 149, exposed independently of their recursion. *)
Parameter value : forall (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)), 1 < tau -> 0 < mu ->
  is_bounded_positive_radius_family mu Q ->
  (nat -> set (X*R)) * (nat -> set (X*R)).
(** Source for [laws]: the initial remainder, selection and
    removal laws of Federer 2.8.12, p. 149. *)
Parameter laws : forall (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) (ht : 1 < tau) (hm : 0 < mu)
    (hQ : is_bounded_positive_radius_family mu Q),
  is_radius_selection_iteration tau Q (@value R X tau mu Q ht hm hQ).1
    (@value R X tau mu Q ht hm hQ).2.
End RadiusSelectionIterationSignature.

Module RadiusSelectionIteration : RadiusSelectionIterationSignature.
(** Source for [value]: the proved private witness of the
    iteration in Federer 2.8.12, p. 149. *)
Definition value (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) (ht : 1 < tau) (hm : 0 < mu)
    (hQ : is_bounded_positive_radius_family mu Q) :=
  projT1 (cid (@radius_selection_iteration_exists R X tau mu Q ht hm hQ)).
(** Source for [laws]: the chosen witness satisfies the
    abstract iteration laws, Federer 2.8.12, p. 149. *)
Lemma laws (R : realType) (X : metricType R)
    (tau mu : R) (Q : set (X*R)) (ht : 1 < tau) (hm : 0 < mu)
    (hQ : is_bounded_positive_radius_family mu Q) :
  is_radius_selection_iteration tau Q (@value R X tau mu Q ht hm hQ).1
    (@value R X tau mu Q ht hm hQ).2.
Proof. exact: projT2 (cid (@radius_selection_iteration_exists R X tau mu Q ht hm hQ)). Qed.
End RadiusSelectionIteration.
