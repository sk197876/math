(** Federer (1969), 2.2.6, p. 63: the first-coordinate cylinders partition
    the sequence space and are open and closed. Source context and
    positive-integer encoding: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceProductTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_sequence_cylinder]: Federer 2.2.6,
    p. 63, the subset N_j whose first coordinate is j. Here
    j is the natural code for the book's positive integer j+1. *)
Definition positive_sequence_cylinder (R : realType) j : set (positive_sequence_space R) :=
  [set x | positive_sequence_coordinates x 0%N = j].
Arguments positive_sequence_cylinder {R} j.

(** Source for [positive_sequence_cylinder_open]: Federer 2.2.6, p. 63: each
    first-coordinate cylinder is open. *)
Lemma positive_sequence_cylinder_open (R : realType) j :
  open (@positive_sequence_cylinder R j).
Proof.
rewrite openE=> x hx.
apply: filterS (positive_sequence_prefix_neighborhood x 1)=> y hy.
have he := hy 0%N (ltnSn 0).
change (positive_sequence_coordinates y 0%N = j).
exact: eq_trans (esym he) hx.
Qed.

(** Source for [positive_sequence_cylinder_closed]: Federer 2.2.6, p. 63:
    each first-coordinate cylinder is closed. Its complement is open, as
    fixing the first coordinate of a point outside the cylinder keeps it
    outside. *)
Lemma positive_sequence_cylinder_closed (R : realType) j :
  closed (@positive_sequence_cylinder R j).
Proof.
have ho : open (~` @positive_sequence_cylinder R j).
  rewrite openE=> x hx.
  apply: filterS (positive_sequence_prefix_neighborhood x 1)=> y hy hj.
  apply: hx; have he := hy 0%N (ltnSn 0).
  exact: eq_trans he hj.
have h := open_closedC ho; by rewrite setCK in h.
Qed.

(** Source for [positive_sequence_cylinders_cover]: Federer
    2.2.6, p. 63, the sequence space is the union of its
    first-coordinate cylinders, indexed by all positive integers. *)
Lemma positive_sequence_cylinders_cover (R : realType) :
  (\bigcup_j (@positive_sequence_cylinder R j)) = setT.
Proof.
apply/seteqP; split; first by move=> x _.
move=> x _; exists (positive_sequence_coordinates x 0%N); by [].
Qed.

(** Source for [positive_sequence_cylinders_disjoint]: supporting
    disjointness of the union in Federer 2.2.6, p. 63: distinct
    first-coordinate values cannot occur at the same point. *)
Lemma positive_sequence_cylinders_disjoint (R : realType) j k :
  j != k -> @positive_sequence_cylinder R j `&` positive_sequence_cylinder k = set0.
Proof.
move=> hne; apply/seteqP; split=> [x [hj hk]|x []].
by move: hne; rewrite -hj -hk eqxx.
Qed.
