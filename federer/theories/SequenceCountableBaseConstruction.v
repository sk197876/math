(** Federer (1969), 2.2.11, p. 68: the sequence space has a countable base,
    needed to construct its universal Suslin set. The basic opens fix a
    finite word of coordinates; finite natural words are countable and are
    enumerated here. The distinguished empty member is added explicitly for
    the closed-set coding boundary case. Source context and convention:
    CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceProductTopology
  SequenceSeparability CountablyInfiniteEnumeration CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [sequence_prefix_open]: supporting open-prefix
    fact for the countable base in Federer 2.2.11, p. 68.
    Agreement with a finite word is an open condition by the
    sequence topology formalised in 2.2.6. *)
Lemma sequence_prefix_open (R : realType) (n : positive_sequence_space R) k :
  open (positive_sequence_prefix n k).
Proof.
rewrite openE=> x hx; apply: filterS (positive_sequence_prefix_neighborhood x k)=> y hy i hi.
exact: eq_trans (hx i hi) (hy i hi).
Qed.

(** Source for [finite_natural_word_enumeration_exists]: supporting
    countable enumeration for Federer 2.2.11, p. 68:
    finite words in positive-integer codes can be indexed by
    naturals. Their distinct lengths supply an infinite subfamily. *)
Lemma finite_natural_word_enumeration_exists :
  exists (encode : seq nat -> nat) (decode : nat -> seq nat),
    cancel encode decode /\ cancel decode encode.
Proof.
apply: (@countably_infinite_enumeration (seq nat) (fun n => nseq n 0%N)).
- exact: countableP.
- move=> n m he; have h := congr1 size he; by rewrite !size_nseq in h.
Qed.

(** Source for [sequence_countable_open_base_exists]: supporting
    countable-base existence for Federer 2.2.11, p. 68. Enumerate all
    finite-prefix opens and add the empty open as the distinguished
    zero-code member. *)
Theorem sequence_countable_open_base_exists (R : realType) :
  exists U : nat -> set (positive_sequence_space R), is_countable_open_base U.
Proof.
have [encode [decode [he hd]]] := finite_natural_word_enumeration_exists.
pose U i := if i is k.+1 then
  positive_sequence_prefix (@positive_sequence_finite_word R (decode k)) (size (decode k)) else set0.
exists U; constructor.
- move=> [|k]; first exact: open0.
  exact: sequence_prefix_open.
- by [].
- move=> V hV x hx.
  have hnb : nbhs x V by rewrite openE in hV; exact: hV x hx.
  have [k hk] := proj1 (positive_sequence_product_neighborhoods x V) hnb.
  pose s := mkseq (positive_sequence_coordinates x) k.
  exists (encode s).+1; rewrite /U he; split.
  + move=> i hi; rewrite /positive_sequence_finite_word positive_sequence_coordinatesK.
    by rewrite /s size_mkseq in hi; rewrite /s nth_mkseq.
  + move=> y hy; apply: hk=> i hi.
    have his : (i < size s)%N by rewrite /s size_mkseq.
    have hh := hy i his.
    by rewrite /positive_sequence_finite_word positive_sequence_coordinatesK /s nth_mkseq in hh.
Qed.
