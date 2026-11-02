(** Opaque cutoff selection for Federer (1969), 2.3.10, p. 80. Source
    context: CauchyIndexSelectionUP.v. *)
From mathcomp Require Import all_boot all_order boolp classical_sets reals constructive_ereal.
From Federer Require Import CauchyIndexSelectionUP CauchyIndexSelectionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.
Module Type CauchyIndexSelectionSignature.
(** Source for [value]: abstract indices N(n) from Federer
    2.3.10, p. 80, for the prescribed tolerances. *)
Parameter value : forall (R : realType) (d : nat -> nat -> \bar R) (b : nat -> R),
  (forall n, exists K, forall i j, (K <= i)%N -> (K <= j)%N -> d i j < (b n)%:E) -> nat -> nat.
(** Source for [laws]: the selection obeys the strict increase
    and Cauchy bounds required in Federer 2.3.10, p. 80. *)
Parameter laws : forall (R : realType) (d : nat -> nat -> \bar R) (b : nat -> R)
  (hc : forall n, exists K, forall i j, (K <= i)%N -> (K <= j)%N -> d i j < (b n)%:E),
  is_cauchy_index_selection d b (@value R d b hc).
End CauchyIndexSelectionSignature.
Module CauchyIndexSelection : CauchyIndexSelectionSignature.
(** Source for [value]: private witness for the index selection
    in Federer 2.3.10, p. 80. *)
Definition value (R : realType) (d : nat -> nat -> \bar R) (b : nat -> R)
  (hc : forall n, exists K, forall i j, (K <= i)%N -> (K <= j)%N -> d i j < (b n)%:E) :=
  projT1 (cid (@cauchy_index_selection_exists R d b hc)).
(** Source for [laws]: proved index-selection specification for
    Federer 2.3.10, p. 80. *)
Lemma laws (R : realType) (d : nat -> nat -> \bar R) (b : nat -> R)
  (hc : forall n, exists K, forall i j, (K <= i)%N -> (K <= j)%N -> d i j < (b n)%:E) :
  is_cauchy_index_selection d b (@value R d b hc).
Proof. exact: projT2 (cid (@cauchy_index_selection_exists R d b hc)). Qed.
End CauchyIndexSelection.
