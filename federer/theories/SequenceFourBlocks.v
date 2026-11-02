(** Supporting regrouping of the ordinary positive-integer sequence in
    Federer (1969), 2.2.9, p. 65, into four-digit blocks. Coordinate indices
    and digits are zero based, as in the public interface of 2.2.6, p. 63.
    The mutually inverse index maps are sealed; no private sequence carrier
    is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SequenceSpace SequenceCoordinates
  NaturalQuadruplingUP NaturalQuadruplingSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [quadruple_digit]: supporting extraction of one
    of four digits in the grouping for Federer 2.2.9,
    p. 65. Only indices less than four are used;
    the default outside that range does not enter the proofs. *)
Definition quadruple_digit (q : (nat * nat) * (nat * nat)) (j : nat) : nat :=
  match j with 0 => q.1.1 | 1 => q.1.2 | 2 => q.2.1 | _ => q.2.2 end.

(** Source for [sequence_four_digits]: supporting consecutive
    four-coordinate block of the sequence in Federer 2.2.9,
    p. 65. The order of the original digits is preserved. *)
Definition sequence_four_digits (a : nat -> nat) k :=
  ((a (k*4+0),a (k*4+1)),(a (k*4+2),a (k*4+3))).

(** Source for [quadruple_digit_collect]: supporting coordinate
    recovery for the four-digit grouping in Federer 2.2.9,
    p. 65. *)
Lemma quadruple_digit_collect a k j :
  j < 4 -> quadruple_digit (sequence_four_digits a k) j = a (k*4+j).
Proof. by case: j=> [|[|[|[|j]]]]. Qed.

(** Source for [sequence_group_four]: supporting regrouping map
    used to construct the classical continued-fraction map of
    Federer 2.2.9, p. 65, from the abstract tree. *)
Definition sequence_group_four (R : realType) (x : positive_sequence_space R) :
    positive_sequence_space R :=
  positive_sequence_from_coordinates (fun k => NaturalQuadrupling.encode
    (sequence_four_digits (positive_sequence_coordinates x) k)).
Arguments sequence_group_four {R} x.

(** Source for [sequence_ungroup_four]: supporting inverse
    regrouping of the sequence in Federer 2.2.9, p. 65. *)
Definition sequence_ungroup_four (R : realType) (x : positive_sequence_space R) :
    positive_sequence_space R :=
  positive_sequence_from_coordinates (fun i => quadruple_digit
    (NaturalQuadrupling.decode (positive_sequence_coordinates x (i %/ 4))) (i %% 4)).
Arguments sequence_ungroup_four {R} x.

(** Source for [sequence_group_fourK]: supporting recovery of
    the original ordinary digit sequence in Federer 2.2.9,
    p. 65, after grouping and ungrouping. *)
Lemma sequence_group_fourK (R : realType) :
  cancel (@sequence_group_four R) (@sequence_ungroup_four R).
Proof.
move=> x; apply: positive_sequence_extensionality=> i.
rewrite /sequence_group_four /sequence_ungroup_four !positive_sequence_coordinatesK.
rewrite (natural_quadrupling_encodeK NaturalQuadrupling.laws) quadruple_digit_collect;
  last by rewrite ltn_mod.
by rewrite -divn_eq.
Qed.

(** Source for [sequence_ungroup_fourK]: supporting recovery of
    the block sequence for Federer 2.2.9, p. 65.
    Thus every block sequence corresponds to ordinary digits. *)
Lemma sequence_ungroup_fourK (R : realType) :
  cancel (@sequence_ungroup_four R) (@sequence_group_four R).
Proof.
move=> x; apply: positive_sequence_extensionality=> k.
rewrite /sequence_group_four /sequence_ungroup_four !positive_sequence_coordinatesK.
rewrite /sequence_four_digits !divnMDl // !modnMDl /= !addn0.
have he q : ((quadruple_digit q 0,quadruple_digit q 1),
  (quadruple_digit q 2,quadruple_digit q 3)) = q by case: q=> [[a b] [c d]].
by rewrite he (natural_quadrupling_decodeK NaturalQuadrupling.laws).
Qed.
