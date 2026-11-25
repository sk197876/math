(** Opaque refined-cover infimum supporting Federer (1969), 2.10.1, p. 170.
    Only its abstract laws are exposed. Source context and corrected
    reference: OpenRefiningEnvelopeUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal.
From Federer Require Import OpenRefiningEnvelopeUP OpenRefiningEnvelopeConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type OpenRefiningEnvelopeSignature.
(** Source for [value]: abstract fixed-cover infimum supporting
    Federer 2.10.1, p. 170. *)
Parameter value : forall (R : realType) (X J : choiceType),
  (J -> set X) -> (J -> \bar R) -> set (set X) -> set X -> \bar R.
(** Source for [laws]: abstract order laws for the refined-cover
    infimum supporting Federer 2.10.1, p. 170. *)
Parameter laws : forall (R : realType) (X J : choiceType) (S : J -> set X)
  (cost : J -> \bar R) (H : set (set X)),
  is_open_refining_envelope S cost H (@value R X J S cost H).
End OpenRefiningEnvelopeSignature.

Module OpenRefiningEnvelope : OpenRefiningEnvelopeSignature.
(** Source for [value]: selection of the proved refined-cover
    infimum witness supporting Federer 2.10.1, p. 170. *)
Definition value (R : realType) (X J : choiceType) (S : J -> set X)
    (cost : J -> \bar R) (H : set (set X)) :=
  projT1 (cid (@open_refining_envelope_exists R X J S cost H)).
(** Source for [laws]: proved abstract laws for the opaque
    refined-cover infimum supporting Federer 2.10.1, p. 170. *)
Lemma laws (R : realType) (X J : choiceType) (S : J -> set X)
    (cost : J -> \bar R) (H : set (set X)) :
  is_open_refining_envelope S cost H (@value R X J S cost H).
Proof. exact: projT2 (cid (@open_refining_envelope_exists R X J S cost H)). Qed.
End OpenRefiningEnvelope.
