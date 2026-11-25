(** Federer (1969), 2.2.10, p. 66: the open-and-closed cylinders of 2.2.6
    allow independent closed pieces and continuous maps to be assembled.
    Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceCylinders OpenCoverPasting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [positive_sequence_cylindrical_paste]: supporting piecewise
    map for Federer 2.2.10, p. 66: the first coordinate selects a map on its
    cylinder. *)
Definition positive_sequence_cylindrical_paste (R : realType) (T : Type)
    (f : nat -> positive_sequence_space R -> T) n :=
  f (positive_sequence_coordinates n 0%N) n.

(** Source for [positive_sequence_cylindrical_pasteE]: supporting
    evaluation on one cylinder for the construction in Federer
    2.2.10, p. 66. *)
Lemma positive_sequence_cylindrical_pasteE (R : realType) (T : Type)
    (f : nat -> positive_sequence_space R -> T) j n :
  positive_sequence_cylinder j n -> positive_sequence_cylindrical_paste f n = f j n.
Proof. by move=> h; rewrite /positive_sequence_cylindrical_paste h. Qed.

(** Source for [positive_sequence_cylindrical_paste_continuous]: supporting
    continuity for Federer 2.2.10, p. 66: continuous maps on the respective
    cylinders paste continuously. *)
Lemma positive_sequence_cylindrical_paste_continuous (R : realType) (T : topologicalType)
    (f : nat -> positive_sequence_space R -> T) :
  (forall j, continuous (f j)) -> continuous (positive_sequence_cylindrical_paste f).
Proof.
move=> hf; apply: (@continuous_from_open_cover_agreement
  [the topologicalType of positive_sequence_space R] T nat
  (@positive_sequence_cylinder R) _ f).
- exact: positive_sequence_cylinder_open.
- move=> n; exists (positive_sequence_coordinates n 0%N); by [].
- exact hf.
- move=> j n hn; exact: positive_sequence_cylindrical_pasteE hn.
Qed.

(** Source for [positive_sequence_cylinderwise_closed]: supporting
    closedness for Federer 2.2.10, p. 66: a subset of N with closed
    intersection with every cylinder is closed. *)
Lemma positive_sequence_cylinderwise_closed (R : realType)
    (B : set (positive_sequence_space R)) :
  (forall j, closed (B `&` positive_sequence_cylinder j)) -> closed B.
Proof.
move=> hB; apply: (@closed_from_open_cover_sections
  [the topologicalType of positive_sequence_space R] nat (@positive_sequence_cylinder R) B).
- exact: positive_sequence_cylinder_open.
- move=> n; exists (positive_sequence_coordinates n 0%N); by [].
- exact hB.
Qed.
