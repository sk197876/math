(** Private existence proof for the refined-cover infimum supporting Federer
    (1969), 2.10.1, p. 170. Use the already sealed fixed-family envelope
    with the proved auxiliary constraint encoding, then recover the abstract
    refined-cover laws. Source context and corrected reference:
    OpenRefiningEnvelopeUP.v. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal.
From Federer Require Import OpenRefiningEnvelopeUP OpenRefiningCoverCost CountableCoverEnvelopeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [open_refining_envelope_exists]: supporting
    existence of the refined-cover infimum in the alternative
    construction of Federer 2.10.1, p. 170. Later proofs
    use only the abstract specification, not this witness. *)
Theorem open_refining_envelope_exists (R : realType) (X J : choiceType)
    (S : J -> set X) (cost : J -> \bar R) (H : set (set X)) :
  exists nu, is_open_refining_envelope S cost H nu.
Proof.
exists (@CountableCoverEnvelope.value R X J S (open_refinement_cost S cost H)).
exact: cover_envelope_as_open_refining (CountableCoverEnvelope.laws S (open_refinement_cost S cost H)).
Qed.
