(** Federer (1969), 2.2.9, p. 65: finite branch prefixes control the inverse
    topology. Source context and reverse-prefix encoding:
    OpenEmbeddingTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceTreePrefixes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [sequence_tree_prefix_coordinates]: supporting inverse-prefix
    implication for Federer 2.2.9, p. 65: equality of the stored prefixes
    means equality of every coordinate through that level. *)
Lemma sequence_tree_prefix_coordinates (R : realType)
    (m n : positive_sequence_space R) k :
  sequence_tree_prefix m k = sequence_tree_prefix n k ->
  forall i, (i < k)%N -> positive_sequence_coordinates m i = positive_sequence_coordinates n i.
Proof.
elim: k=> [|k IH] he i hi; first by move: hi; rewrite ltn0.
have hh := congr1 (head 0%N) he.
have ht := congr1 behead he.
change (positive_sequence_coordinates m k = positive_sequence_coordinates n k) in hh.
change (sequence_tree_prefix m k = sequence_tree_prefix n k) in ht.
case: (ltngtP i k)=> hik.
- exact: IH ht i hik.
- by move: hi; rewrite ltnS leqNgt hik.
- by rewrite hik.
Qed.
