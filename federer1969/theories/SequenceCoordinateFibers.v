(** Federer (1969), 2.2.11, p. 68: a single coordinate of the sequence
    parameter selects a basic open set. The coordinate fibers are open and
    closed by the 2.2.6 product topology. the latter explicitly treats the
    first-coordinate cylinders. Source context: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceCoordinateContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [positive_sequence_coordinate_fiber_open]: supporting
    openness used in the closedness proof of C in Federer
    2.2.11, p. 68: fixing any one discrete coordinate
    gives an open subset of the sequence space. *)
Lemma positive_sequence_coordinate_fiber_open (R : realType) i j :
  open [set n : positive_sequence_space R | positive_sequence_coordinates n i = j].
Proof.
rewrite openE=> n hn.
have h := positive_sequence_coordinate_neighborhood n i.
apply: filterS h=> m hm; by rewrite /= hm hn.
Qed.

(** Source for [positive_sequence_coordinate_fiber_closed]: supporting
    closedness of coordinate fibers for Federer 2.2.11,
    p. 68: the same local constancy applies to their complements. *)
Lemma positive_sequence_coordinate_fiber_closed (R : realType) i j :
  closed [set n : positive_sequence_space R | positive_sequence_coordinates n i = j].
Proof.
rewrite -openC openE=> n hn.
have h := positive_sequence_coordinate_neighborhood n i.
apply: filterS h=> m hm he; apply: hn; exact: eq_trans (esym hm) he.
Qed.
