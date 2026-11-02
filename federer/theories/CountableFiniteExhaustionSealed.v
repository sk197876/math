(** Opaque finite-exhaustion interface supporting Federer (1969), 2.4.8, p.
    84. Source context and abstract laws: CountableFiniteExhaustionUP.v. *)
From mathcomp Require Import all_boot finmap boolp classical_sets cardinality.
From Federer Require Import CountableFiniteExhaustionUP CountableFiniteExhaustionConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Module Type CountableFiniteExhaustionSignature.
(** Source for [value]: abstract exhaustion used for the
    countable indexing set in Federer 2.4.8, p. 84. *)
Parameter value : forall (J : choiceType) (D : set J), countable D -> nat -> {fset J}.
(** Source for [laws]: finite, increasing, exhaustive indexing
    laws supporting Federer 2.4.8, p. 84. *)
Parameter laws : forall (J : choiceType) (D : set J) (hD : countable D),
  is_countable_finite_exhaustion D (@value J D hD).
End CountableFiniteExhaustionSignature.
Module CountableFiniteExhaustion : CountableFiniteExhaustionSignature.
(** Source for [value]: private selection of a proved
    exhaustion for Federer 2.4.8, p. 84. *)
Definition value (J : choiceType) (D : set J) (hD : countable D) :=
  projT1 (cid (countable_finite_exhaustion_exists hD)).
(** Source for [laws]: the selected exhaustion satisfies the
    laws required for Federer 2.4.8, p. 84. *)
Lemma laws (J : choiceType) (D : set J) (hD : countable D) :
  is_countable_finite_exhaustion D (@value J D hD).
Proof. exact: projT2 (cid (countable_finite_exhaustion_exists hD)). Qed.
End CountableFiniteExhaustion.
