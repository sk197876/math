(** Federer (1969), 2.2.12, p. 69: coordinate bounds defining Z_i and the
    truncation of a sequence after its first i coordinates, filling the
    remaining positive coordinates with ones. All operations use the public
    coordinate laws; their natural codes fill with zero. *)
From mathcomp Require Import all_boot boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceProductTopology
  SequenceCoordinateContinuity SequenceBoxes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [sequence_coordinate_bound]: direct single-coordinate
    condition n_i<=m_i in Federer 2.2.12, p. 69,
    expressed in zero-based positive-integer codes. *)
Definition sequence_coordinate_bound (R : realType) i m : set (positive_sequence_space R) :=
  [set n | (positive_sequence_coordinates n i <= m)%N].

(** Source for [sequence_coordinate_bound_closed]: supporting
    closedness of each coordinate constraint in Federer 2.2.12,
    p. 69, needed to preserve closedness of the witnesses Z_i.
    Coordinate values are locally constant by 2.2.6. *)
Lemma sequence_coordinate_bound_closed (R : realType) i m :
  closed (@sequence_coordinate_bound R i m).
Proof.
rewrite -openC openE=> n hn.
apply: filterS (positive_sequence_coordinate_neighborhood n i)=> n' he hbound.
apply: hn; move: hbound; by rewrite /sequence_coordinate_bound /= he.
Qed.

(** Source for [sequence_box_prefix]: supporting finite portion
    of the bounds defining K in Federer 2.2.12, p. 69.
    At stage k only the first k natural-code coordinates are bounded. *)
Definition sequence_box_prefix (R : realType) (b : nat -> nat) k :
    set (positive_sequence_space R) :=
  [set n | forall i, (i < k)%N -> (positive_sequence_coordinates n i <= b i)%N].

(** Source for [sequence_box_truncate]: direct truncation used
    in the last paragraph of Federer 2.2.12, p. 69:
    retain the first k positive coordinates and put ones afterwards. *)
Definition sequence_box_truncate (R : realType) (n : positive_sequence_space R) k :=
  @positive_sequence_from_coordinates R
    (fun i => if (i < k)%N then positive_sequence_coordinates n i else 0%N).

(** Source for [sequence_box_truncate_member]: supporting membership
    of the truncated sequence in K in Federer 2.2.12,
    p. 69. Finite prefix bounds suffice, since every remaining
    positive coordinate is the smallest permitted value, one. *)
Lemma sequence_box_truncate_member (R : realType) (b : nat -> nat)
    (n : positive_sequence_space R) k : sequence_box_prefix b k n ->
  sequence_coordinate_box b (sequence_box_truncate n k).
Proof.
move=> hn i; rewrite /sequence_box_truncate positive_sequence_coordinatesK.
case: ifP=> hi; [exact: hn i hi|exact: leq0n].
Qed.

(** Source for [sequence_box_truncate_prefix]: supporting initial
    coordinate agreement in the truncation argument of Federer
    2.2.12, p. 69. The zero-length prefix is included. *)
Lemma sequence_box_truncate_prefix (R : realType) (n : positive_sequence_space R) k :
  positive_sequence_prefix (sequence_box_truncate n k) k n.
Proof. move=> i hi; by rewrite /sequence_box_truncate positive_sequence_coordinatesK hi. Qed.

(** Source for [sequence_finite_prefix_open]: supporting open
    cylinders for the compactness step of Federer 2.2.12,
    p. 69. Agreement with any finite initial word is an
    open condition in the topology of 2.2.6. *)
Lemma sequence_finite_prefix_open (R : realType) (n : positive_sequence_space R) k :
  open (positive_sequence_prefix n k).
Proof.
rewrite openE=> x hx; apply: filterS (positive_sequence_prefix_neighborhood x k)=> y hy i hi.
exact: eq_trans (hx i hi) (hy i hi).
Qed.
