(** Federer (1969), 2.2.10, p. 65, definition by projection of a closed
    subset of X times the sequence space. The working erratum, p. 1, book p.
    65 line 20, replaces "can mean" by "mean". *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_suslin_set]: direct definition from Federer 2.2.10, p.
    65, first paragraph, with the wording corrected by erratum p. 1, book p.
    65 line 20. A Suslin set is a first-coordinate projection of a closed
    subset of X times N. The scalar parameter fixes Federer's sequence
    metric; it imposes no metric on X. *)
Definition is_suslin_set (R : realType) (T : topologicalType) (S : set T) : Prop :=
  exists C : set (T * positive_sequence_space R), closed C /\ fst @` C = S.

(** Source for [is_univalent_closed_projection]: supporting specification of
    the family F in Federer 2.2.10, p. 66: C is closed, its first-coordinate
    projection has image S, and that projection is one-to-one on C. These
    are proved properties of a witness, not unproved global axioms. *)
Record is_univalent_closed_projection (R : realType) (T : topologicalType)
    (S : set T) (C : set (T * positive_sequence_space R)) : Prop := {
  univalent_projection_closed : closed C;
  univalent_projection_image : fst @` C = S;
  univalent_projection_injective : forall p q, C p -> C q -> p.1 = q.1 -> p = q
}.

(** Source for [has_univalent_closed_projection]: Federer 2.2.10, p. 66, the
    family F of sets represented by one-to-one closed projections. Existence
    is proved separately from this specification. *)
Definition has_univalent_closed_projection (R : realType) (T : topologicalType)
    (S : set T) : Prop :=
  exists C : set (T * positive_sequence_space R), is_univalent_closed_projection S C.

(** Source for [univalent_closed_projection_is_suslin]: supporting
    inclusion of F in the Suslin sets in Federer 2.2.10,
    p. 66: forget the extra injectivity condition. *)
Lemma univalent_closed_projection_is_suslin (R : realType) (T : topologicalType)
    (S : set T) : has_univalent_closed_projection R S -> is_suslin_set R S.
Proof. move=> [C hC]; exists C; split; [exact: univalent_projection_closed hC|exact: univalent_projection_image hC]. Qed.
