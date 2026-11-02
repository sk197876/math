(** Federer (1969), 2.2.9, p. 65: supporting agreement of grouped cylinder
    prefixes with the actual ordinary-digit continued fraction. Four-digit
    grouping is used only in the proof; this module identifies every grouped
    prefix with its literal consecutive digits. Source context:
    ContinuedFractionBranches.v and FiniteContinuedFractions.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceTreePrefixes
  SequenceFourBlocks NaturalQuadruplingUP NaturalQuadruplingSealed
  ContinuedFractionWords FiniteContinuedFractions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [continued_fraction_block_digits]: supporting
    expansion of the reversed tree word into ordinary digits
    in the continued fraction of Federer 2.2.9, p. 65. *)
Fixpoint continued_fraction_block_digits
    (d : nat -> (nat * nat) * (nat * nat)) (s : seq nat) : seq nat :=
  if s is j :: r then continued_fraction_block_digits d r ++ quadruple_digits (d j)
  else [::].

(** Source for [continued_fraction_block_digitsE]: supporting
    agreement of the expanded ordinary digits with the finite
    grouped expression for Federer 2.2.9, p. 65. *)
Lemma continued_fraction_block_digitsE (R : realType) d s (t : R) :
  finite_continued_fraction (continued_fraction_block_digits d s) t =
  continued_fraction_word d s t.
Proof.
elim: s t=> [|j s IH] t //=.
by rewrite finite_continued_fraction_cat finite_continued_fraction_block IH.
Qed.

(** Source for [sequence_four_digits_list]: supporting consecutive
    order of the four digits used for Federer 2.2.9, p. 65. *)
Lemma sequence_four_digits_list a k :
  quadruple_digits (sequence_four_digits a k) = map a (iota (k*4) 4).
Proof. by rewrite /quadruple_digits /sequence_four_digits /= !addnS !addn0. Qed.

(** Source for [continued_fraction_grouped_prefix_digits]:
    supporting exact prefix identity for Federer 2.2.9,
    p. 65: k tree levels contain the first 4k
    ordinary digits, in their original order. *)
Lemma continued_fraction_grouped_prefix_digits (R : realType)
    (n : positive_sequence_space R) k :
  continued_fraction_block_digits NaturalQuadrupling.decode
    (sequence_tree_prefix (sequence_group_four n) k) =
  map (positive_sequence_coordinates n) (iota 0 (k*4)).
Proof.
elim: k=> [|k IH] //=.
rewrite /sequence_group_four positive_sequence_coordinatesK
  (natural_quadrupling_encodeK NaturalQuadrupling.laws) sequence_four_digits_list IH.
change (map (positive_sequence_coordinates n) (iota 0 (k*4)) ++
  map (positive_sequence_coordinates n) (iota (k*4) 4) =
  map (positive_sequence_coordinates n) (iota 0 (4+k*4))).
by rewrite [(4+k*4)%N]addnC iotaD map_cat add0n.
Qed.

(** Source for [continued_fraction_grouped_prefixE]: supporting
    literal fraction identity for the cylinders used to construct
    the map in Federer 2.2.9, p. 65. *)
Lemma continued_fraction_grouped_prefixE (R : realType)
    (n : positive_sequence_space R) k (t : R) :
  continued_fraction_word NaturalQuadrupling.decode
    (sequence_tree_prefix (sequence_group_four n) k) t =
  finite_continued_fraction (map (positive_sequence_coordinates n) (iota 0 (k*4))) t.
Proof. by rewrite -continued_fraction_block_digitsE continued_fraction_grouped_prefix_digits. Qed.
