(** Successive selections in Federer (1969), 2.8.12, pp. 148–149. At each
    stage apply 2.8.10 to the remaining parameters and remove the selected
    subset. Formal stage zero corresponds to the book's first nonempty
    selection stage: Q_0 here is printed Q_1=Q, and R_0 here is printed R_1.
    we retain Federer's parameter-level iteration. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import RadiusCoverSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_radius_selection_iteration]: the inductive
    families in the proof of Federer 2.8.12, p. 149.
    The initial eligible set is Q; every selected stage satisfies
    both conditions of 2.8.10; the next remainder removes it.
    These laws specify the iteration independently of a recursion. *)
Record is_radius_selection_iteration (R : realType) (X : metricType R)
    (tau : R) (Q : set (X*R)) (W S : nat -> set (X*R)) : Prop := {
  (** Source for [radius_iteration_initial]: Q_1=Q after
      the preliminary empty step, Federer 2.8.12, p. 149. *)
  radius_iteration_initial : W 0 = Q;
  (** Source for [radius_iteration_selection]: conditions
      (1) and (2) at each stage, Federer 2.8.12, p. 149. *)
  radius_iteration_selection : forall n, is_radius_cover_selection tau (W n) (S n);
  (** Source for [radius_iteration_remainder]: remove the
      preceding selection, Federer 2.8.12, p. 149. *)
  radius_iteration_remainder : forall n, W n.+1 = W n `\` S n
}.
