(** Federer (1969), 2.2.6, p. 63: public metric sequence-space interface.
    The metric laws are proved from the sealed coordinate and series
    specifications; the general metric hierarchy supplies only topological
    notation. Source context and encoding: SequenceSpaceUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpaceUP SequenceMetricLaws SequenceSpaceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_sequence_space]: Federer 2.2.6,
    p. 63, the abstract sequence carrier equipped below with its
    exact metric over the selected real field. *)
Definition positive_sequence_space (R : realType) : Type := SequenceSpace.carrier.
HB.instance Definition _ (R : realType) := Choice.copy (positive_sequence_space R) SequenceSpace.carrier.

(** Source for [positive_sequence_coordinates]: Federer
    2.2.6, p. 63, public coordinate map; natural codes represent
    the corresponding positive integers by adding one. *)
Definition positive_sequence_coordinates (R : realType)
    (s : positive_sequence_space R) : nat -> nat := SequenceSpace.coordinates s.

(** Source for [positive_sequence_coordinates_laws]: Federer
    2.2.6, p. 63, public coordinate representation is bijective. *)
Lemma positive_sequence_coordinates_laws (R : realType) :
  is_positive_sequence_representation (@positive_sequence_coordinates R).
Proof.
constructor.
- exact: (sequence_coordinates_injective SequenceSpace.coordinate_laws).
- exact: (sequence_coordinates_surjective SequenceSpace.coordinate_laws).
Qed.
Arguments positive_sequence_coordinates_laws R : clear implicits.

(** Source for [positive_sequence_distance]: Federer 2.2.6,
    p. 63, public real distance from the sealed series witness. *)
Definition positive_sequence_distance (R : realType)
    (s t : positive_sequence_space R) : R := @SequenceSpace.distance R s t.

(** Source for [positive_sequence_distance_specification]: Federer
    2.2.6, p. 63, public distance satisfies the exact weighted
    coordinate series formula. *)
Lemma positive_sequence_distance_specification (R : realType) :
  is_positive_sequence_metric (@positive_sequence_coordinates R) (@positive_sequence_distance R).
Proof. exact: SequenceSpace.distance_laws. Qed.
Arguments positive_sequence_distance_specification R : clear implicits.

HB.instance Definition _ (R : realType) := isMetric.Build R (positive_sequence_space R)
  (@positive_sequence_distance_self R _ _ _ (positive_sequence_distance_specification R))
  (@positive_sequence_distance_separates R _ _ (positive_sequence_coordinates_laws R) _ (positive_sequence_distance_specification R))
  (@positive_sequence_distance_symmetry R _ _ _ (positive_sequence_distance_specification R))
  (fun y x z => @positive_sequence_distance_triangle R _ _ _ (positive_sequence_distance_specification R) x y z).

(** Source for [positive_sequence_metric_distanceE]: Federer
    2.2.6, p. 63, the hierarchy's distance is exactly the
    public distance already specified by the printed series. *)
Lemma positive_sequence_metric_distanceE (R : realType) (x y : positive_sequence_space R) :
  mdist x y = positive_sequence_distance x y.
Proof. by []. Qed.
