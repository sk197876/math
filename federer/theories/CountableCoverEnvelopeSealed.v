(** Sealed fixed-family covering infimum from Federer (1969), 2.10.1, p.
    170, used for the local counterexample in 2.3.8, p. 78. Only the laws
    are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import CountableCoverEnvelopeUP CountableCoverEnvelopeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Module Type COUNTABLE_COVER_ENVELOPE.
  (** Source for [value]: abstract covering infimum in Federer
      2.10.1, p. 170, supporting the 2.3.8 example. *)
  Parameter value : forall (R : realType) (X J : choiceType),
    (J -> set X) -> (J -> \bar R) -> set X -> \bar R.
  (** Source for [laws]: defining infimum laws from Federer
      2.10.1, p. 170, exposed by the sealed interface. *)
  Parameter laws : forall (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R),
    is_countable_cover_envelope S cost (@value R X J S cost).
End COUNTABLE_COVER_ENVELOPE.

Module CountableCoverEnvelope : COUNTABLE_COVER_ENVELOPE.
(** Source for [value]: sealed witness of the covering infimum
    in Federer 2.10.1, p. 170. *)
Definition value (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) :=
  projT1 (cid (@countable_cover_envelope_exists R X J S cost)).
(** Source for [laws]: abstract defining laws of the sealed
    covering infimum in Federer 2.10.1, p. 170. *)
Lemma laws (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) :
    is_countable_cover_envelope S cost (@value R X J S cost).
Proof. exact: projT2 (cid (@countable_cover_envelope_exists R X J S cost)). Qed.
End CountableCoverEnvelope.
