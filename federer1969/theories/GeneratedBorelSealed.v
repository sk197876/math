(** Federer (1969), 2.2.1, pp. 59-60: sealed generated Borel family,
    exposing only its smallest-containing-family laws. Source context:
    BorelFamilyUP.v. The intersection witness remains private. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import BorelFamilyUP GeneratedBorelConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type GeneratedBorelSignature.
(** Source for [value]: Federer 2.2.1, pp. 59-60,
    abstract generated-family operator on subsets of X. *)
Parameter value : forall (I : choiceType) (X : set I) (S : set (set I)),
  (forall A, S A -> A `<=` X) -> set (set I).
(** Source for [laws]: Federer 2.2.1, pp. 59-60,
    the operator satisfies the smallest-containing-Borel-family laws. *)
Parameter laws : forall (I : choiceType) (X : set I) (S : set (set I))
  (hS : forall A, S A -> A `<=` X),
  is_generated_borel_family X S (@value I X S hS).
End GeneratedBorelSignature.

Module GeneratedBorel : GeneratedBorelSignature.
(** Source for [value]: Federer 2.2.1, pp. 59-60,
    private choice of the proved intersection witness. *)
Definition value (I : choiceType) (X : set I) (S : set (set I))
    (hS : forall A, S A -> A `<=` X) :=
  projT1 (cid (generated_borel_family_exists hS)).
(** Source for [laws]: Federer 2.2.1, pp. 59-60,
    the chosen witness obeys its abstract specification. *)
Lemma laws (I : choiceType) (X : set I) (S : set (set I))
    (hS : forall A, S A -> A `<=` X) :
  is_generated_borel_family X S (value hS).
Proof. exact: projT2 (cid (generated_borel_family_exists hS)). Qed.
End GeneratedBorel.
