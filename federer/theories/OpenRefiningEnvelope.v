(** Public fixed-cover envelope supporting Federer (1969), 2.10.1, p. 170.
    All results use the sealed infimum laws; the implementation is not
    exposed. Source context, corrected reference and topological convention:
    OpenRefiningEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import OpenRefiningEnvelopeUP OpenRefiningEnvelopeSealed OpenRefiningCoverCost MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [open_refining_envelope]: public fixed-cover
    infimum in the alternative construction supporting Federer
    2.10.1, p. 170, through its abstract specification. *)
Definition open_refining_envelope (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) :=
  @OpenRefiningEnvelope.value R X J S cost H.

(** Source for [open_refining_envelope_specification]: abstract
    covering-infimum laws supporting Federer 2.10.1, p. 170. *)
Lemma open_refining_envelope_specification (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) :
  is_open_refining_envelope S cost H (open_refining_envelope S cost H).
Proof. exact: OpenRefiningEnvelope.laws. Qed.

(** Source for [open_refining_envelope_measure]: public fixed-cover
    measure assertion supporting the alternative construction
    in Federer 2.10.1, p. 170. *)
Theorem open_refining_envelope_measure (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) :
  (forall j, (0<=cost j)%E) -> is_measure (open_refining_envelope S cost H).
Proof. exact: open_refining_envelope_is_measure (open_refining_envelope_specification S cost H). Qed.
