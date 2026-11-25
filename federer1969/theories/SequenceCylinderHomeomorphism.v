(** Federer (1969), 2.2.6, p. 63: each first-coordinate cylinder is
    homeomorphic with the entire sequence space. The inverse constructed
    here extends continuously to the whole ambient sequence space. Source
    editions and encoding: SequenceSpaceUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceProductTopology SequenceCylinders.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [positive_sequence_prefix_continuous]: supporting
    continuity criterion for Federer 2.2.6, p. 63: at each point,
    a map that fixes any requested finite output prefix by fixing
    a finite input prefix is continuous for the product topology. *)
Lemma positive_sequence_prefix_continuous (R : realType)
    (f : positive_sequence_space R -> positive_sequence_space R) :
  (forall x N, exists M, forall y,
    positive_sequence_prefix x M y -> positive_sequence_prefix (f x) N (f y)) ->
  continuous f.
Proof.
move=> hf x U hu.
have [N hN] := proj1 (positive_sequence_product_neighborhoods (f x) U) hu.
have [M hM] := hf x N.
apply: filterS (positive_sequence_prefix_neighborhood x M)=> y hy.
exact: hN (f y) (hM y hy).
Qed.

(** Source for [positive_sequence_prepend]: Federer 2.2.6, p. 63, supporting
    cylinder map: insert the fixed first coordinate j before an arbitrary
    sequence. *)
Definition positive_sequence_prepend (R : realType) j (x : positive_sequence_space R) : positive_sequence_space R :=
  positive_sequence_from_coordinates (fun i => if i is k.+1 then positive_sequence_coordinates x k else j).

(** Source for [positive_sequence_tail]: Federer 2.2.6, p. 63, supporting
    inverse map: delete the first coordinate. *)
Definition positive_sequence_tail (R : realType) (x : positive_sequence_space R) : positive_sequence_space R :=
  positive_sequence_from_coordinates (fun i => positive_sequence_coordinates x i.+1).

(** Source for [positive_sequence_prepend_head]: Federer
    2.2.6, p. 63, the inserted first coordinate places the
    image in its designated cylinder. *)
Lemma positive_sequence_prepend_head (R : realType) j (x : positive_sequence_space R) :
  positive_sequence_coordinates (positive_sequence_prepend j x) 0%N = j.
Proof. by rewrite /positive_sequence_prepend positive_sequence_coordinatesK. Qed.

(** Source for [positive_sequence_prepend_successor]: Federer
    2.2.6, p. 63, head insertion shifts every old coordinate
    one place to the right. *)
Lemma positive_sequence_prepend_successor (R : realType) j (x : positive_sequence_space R) i :
  positive_sequence_coordinates (positive_sequence_prepend j x) i.+1 = positive_sequence_coordinates x i.
Proof. by rewrite /positive_sequence_prepend positive_sequence_coordinatesK. Qed.

(** Source for [positive_sequence_tail_coordinate]: Federer
    2.2.6, p. 63, tail deletion shifts every remaining
    coordinate one place to the left. *)
Lemma positive_sequence_tail_coordinate (R : realType) (x : positive_sequence_space R) i :
  positive_sequence_coordinates (positive_sequence_tail x) i = positive_sequence_coordinates x i.+1.
Proof. by rewrite /positive_sequence_tail positive_sequence_coordinatesK. Qed.

(** Source for [positive_sequence_tail_prepend]: Federer 2.2.6, p. 63,
    supporting left inverse in the cylinder homeomorphism. *)
Lemma positive_sequence_tail_prepend (R : realType) j (x : positive_sequence_space R) :
  positive_sequence_tail (positive_sequence_prepend j x) = x.
Proof.
apply: positive_sequence_extensionality=> i.
by rewrite positive_sequence_tail_coordinate positive_sequence_prepend_successor.
Qed.

(** Source for [positive_sequence_prepend_tail]: Federer
    2.2.6, p. 63, supporting right inverse on the designated
    first-coordinate cylinder. The cylinder hypothesis is essential. *)
Lemma positive_sequence_prepend_tail (R : realType) j (x : positive_sequence_space R) :
  positive_sequence_cylinder j x -> positive_sequence_prepend j (positive_sequence_tail x) = x.
Proof.
move=> hx; apply: positive_sequence_extensionality=> i; case: i=> [|i].
- rewrite positive_sequence_prepend_head; exact: esym hx.
- by rewrite positive_sequence_prepend_successor positive_sequence_tail_coordinate.
Qed.

(** Source for [positive_sequence_prepend_continuous]: Federer 2.2.6, p. 63,
    continuity of the cylinder parametrisation, verified by finite-prefix
    agreement. *)
Lemma positive_sequence_prepend_continuous (R : realType) j :
  continuous (@positive_sequence_prepend R j).
Proof.
apply: positive_sequence_prefix_continuous=> x N; exists N=> y hy i hi.
case: i hi=> [|i] hi; first by rewrite !positive_sequence_prepend_head.
rewrite !positive_sequence_prepend_successor; apply: hy.
exact: ltn_trans (ltnSn i) hi.
Qed.

(** Source for [positive_sequence_tail_continuous]: Federer
    2.2.6, p. 63, continuity of the inverse to the cylinder
    parametrisation. It extends to all sequences, requiring one
    additional input coordinate for any given output prefix. *)
Lemma positive_sequence_tail_continuous (R : realType) :
  continuous (@positive_sequence_tail R).
Proof.
apply: positive_sequence_prefix_continuous=> x N; exists N.+1=> y hy i hi.
rewrite !positive_sequence_tail_coordinate; apply: hy; by rewrite ltnS.
Qed.

(** Source for [positive_sequence_cylinder_homeomorphism]: Federer 2.2.6, p.
    63, direct homeomorphism assertion given by explicit continuous maps: f
    has image the cylinder, g is its inverse there, and g extends
    continuously to the ambient space. *)
Theorem positive_sequence_cylinder_homeomorphism (R : realType) j :
  exists f g : positive_sequence_space R -> positive_sequence_space R,
    f @` setT = positive_sequence_cylinder j /\
    cancel f g /\ (forall y, positive_sequence_cylinder j y -> f (g y) = y) /\
    continuous f /\ continuous g.
Proof.
exists (@positive_sequence_prepend R j), (@positive_sequence_tail R); split.
- apply/seteqP; split.
  + move=> y [x _ <-]; exact: positive_sequence_prepend_head.
  + move=> y hy; exists (positive_sequence_tail y); first exact Logic.I.
    exact: positive_sequence_prepend_tail hy.
- split; first exact: positive_sequence_tail_prepend.
  split; first exact: positive_sequence_prepend_tail.
  split; [exact: positive_sequence_prepend_continuous|exact: positive_sequence_tail_continuous].
Qed.
