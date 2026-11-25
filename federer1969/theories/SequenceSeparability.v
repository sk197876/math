(** Federer (1969), 2.2.6, p. 63: the sequence metric space is separable.
    Finite words followed by the constant positive integer one give a
    countable dense set. Realisation uses the sealed coordinate laws, not
    the private function carrier. Source context and zero-based encoding:
    SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceProductTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_sequence_finite_word]: Federer
    2.2.6, p. 63, supporting dense-set construction: realise
    a finite word of positive-integer codes, with all later codes
    zero, representing the positive integer one. *)
Definition positive_sequence_finite_word (R : realType) (s : seq nat) :
    positive_sequence_space R := positive_sequence_from_coordinates (nth 0%N s).

(** Source for [positive_sequence_finite_words_countable]: Federer
    2.2.6, p. 63, supporting countability of the finite-word
    dense set, as an image of the countable set of finite natural lists. *)
Lemma positive_sequence_finite_words_countable (R : realType) :
  countable (@positive_sequence_finite_word R @` setT).
Proof.
apply: sub_countable (card_image_le _ _) _; exact: countableP.
Qed.

(** Source for [positive_sequence_finite_words_dense]: Federer 2.2.6, p. 63,
    supporting density: truncate a sequence after the finite prefix required
    by an open neighborhood. That finite word followed by ones lies in the
    neighborhood. *)
Lemma positive_sequence_finite_words_dense (R : realType) :
  dense (@positive_sequence_finite_word R @` setT).
Proof.
move=> U [x hx] ho; have hnb : nbhs x U.
  rewrite openE in ho; exact: ho x hx.
have [N hN] := proj1 (positive_sequence_product_neighborhoods x U) hnb.
pose s := mkseq (positive_sequence_coordinates x) N.
exists (@positive_sequence_finite_word R s); split.
- apply: hN=> i hi.
  by rewrite /positive_sequence_finite_word positive_sequence_coordinatesK /s nth_mkseq.
- by exists s.
Qed.

(** Source for [positive_sequence_separable]: Federer 2.2.6, p. 63, direct
    separability assertion: there is a countable dense subset of the
    sequence space. The theorem exposes existence, not the dense-set
    implementation. *)
Theorem positive_sequence_separable (R : realType) :
  exists D : set (positive_sequence_space R), countable D /\ dense D.
Proof.
exists (@positive_sequence_finite_word R @` setT); split.
- exact: positive_sequence_finite_words_countable.
- exact: positive_sequence_finite_words_dense.
Qed.
