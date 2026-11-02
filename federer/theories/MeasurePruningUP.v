(** Federer (1969), 2.2.12, p. 69: abstract coordinate pruning with summably
    small losses in the regular measure. We use the already proved
    half-error budget delta*2^-(k+2), a strengthening of the printed budget
    delta*2^-(k+1). This leaves room in the final non-strict tolerance
    bound. Source context and expanded continuity reference:
    RegularProjectionLoss.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import SequenceSpace CoordinatePruningUP GeometricErrorBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_coordinate_pruning]: abstract laws
    of the choices m_i,Z_i in Federer 2.2.12, p. 69.
    The recursion matches the coordinate cuts exactly. Losses
    are written additively, equivalently for the finite measures
    used in the theorem, with the documented half-error budget. *)
Record is_measure_coordinate_pruning (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (Z : set (X * positive_sequence_space R))
    (delta : R) (b : nat -> nat) (F : nat -> set (X * positive_sequence_space R)) : Prop := {
  measure_pruning_recursion : is_coordinate_pruning Z b F;
  measure_pruning_positive_error : (0 < delta)%R;
  measure_pruning_step_loss : forall k, gamma (fst @` F k) <
    gamma (fst @` F k.+1) + (geometric_error_budget delta k)%:E
}.
