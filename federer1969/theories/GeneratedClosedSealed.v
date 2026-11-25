(** Federer (1969), 2.2.1, pp. 59-60: sealed generated countably closed
    family, exposing only its smallest-containing-family laws. Source
    editions: CountablyClosedFamilyUP.v. The intersection witness remains
    private. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import CountablyClosedFamilyUP GeneratedClosedConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type GeneratedClosedSignature.
(** Source for [value]: Federer 2.2.1, pp. 59-60,
    abstract generated-family operator on subsets of X. *)
Parameter value : forall (d : bool) (I : choiceType) (X : set I) (S : set (set I)),
  (forall A, S A -> A `<=` X) -> set (set I).
(** Source for [laws]: Federer 2.2.1, pp. 59-60,
    the operator satisfies the smallest-containing-closed-family laws. *)
Parameter laws : forall (d : bool) (I : choiceType) (X : set I) (S : set (set I))
  (hS : forall A, S A -> A `<=` X),
  is_generated_closed_family d X S (@value d I X S hS).
End GeneratedClosedSignature.

Module GeneratedClosed : GeneratedClosedSignature.
(** Source for [value]: Federer 2.2.1, pp. 59-60,
    private choice of the proved intersection witness. *)
Definition value (d : bool) (I : choiceType) (X : set I) (S : set (set I))
    (hS : forall A, S A -> A `<=` X) :=
  projT1 (cid (generated_closed_family_exists d hS)).
(** Source for [laws]: Federer 2.2.1, pp. 59-60,
    the chosen witness obeys its abstract specification. *)
Lemma laws (d : bool) (I : choiceType) (X : set I) (S : set (set I))
    (hS : forall A, S A -> A `<=` X) :
  is_generated_closed_family d X S (value d hS).
Proof. exact: projT2 (cid (generated_closed_family_exists d hS)). Qed.
End GeneratedClosed.
