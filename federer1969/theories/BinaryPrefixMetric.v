(** The binary first-difference metric for a project test of
    Federer 2.10.11, p. 176. Its representation is hidden by a
    signature exposing only the earlier independent distance laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import BinarySequenceCylinders BinaryPrefixDistanceUP
  BinaryPrefixDistanceExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module Type BinaryPrefixDistanceSignature.
(** Source for [distance]: the first-difference distance used in
    a project test of the spherical variant in Federer 2.10.11,
    p. 176; selected only after its independent specification. *)
Parameter distance:forall R:realType,binary_sequence_space->binary_sequence_space->R.
(** Source for [laws]: the original independent first-difference
    laws for the project test of Federer 2.10.11, p. 176. *)
Parameter laws:forall R:realType,is_binary_prefix_distance (@distance R).
End BinaryPrefixDistanceSignature.
Module BinaryPrefixDistance:BinaryPrefixDistanceSignature.
(** Source for [distance]: private witness from proved distance
    existence for the project test of Federer 2.10.11, p. 176. *)
Definition distance (R:realType):=projT1 (cid (binary_prefix_distance_exists R)).
(** Source for [laws]: the selected distance satisfies the earlier
    independent laws, supporting the project test of Federer
    2.10.11, p. 176. *)
Lemma laws (R:realType):is_binary_prefix_distance (@distance R).
Proof. exact:projT2 (cid (binary_prefix_distance_exists R)). Qed.
End BinaryPrefixDistance.

(** Source for [binary_prefix_metric]: binary sequences with the
    opaque first-difference distance, supporting the project test of
    Federer 2.10.11, p. 176. *)
Definition binary_prefix_metric (R:realType):Type:=binary_sequence_space.
HB.instance Definition _ (R:realType):=Choice.copy (binary_prefix_metric R) binary_sequence_space.
HB.instance Definition _ (R:realType):=isMetric.Build R (binary_prefix_metric R)
  (binary_prefix_distance_self (BinaryPrefixDistance.laws R))
  (binary_prefix_distance_separates (BinaryPrefixDistance.laws R))
  (binary_prefix_distance_symmetric (BinaryPrefixDistance.laws R))
  (fun y x z=>binary_prefix_distance_triangle (BinaryPrefixDistance.laws R) x y z).

(** Source for [binary_prefix_metric_distance]: the hierarchy's
    distance agrees with the sealed first-difference value in the
    supporting project test of Federer 2.10.11, p. 176. *)
Lemma binary_prefix_metric_distance (R:realType) (x y:binary_prefix_metric R):
  mdist x y=BinaryPrefixDistance.distance R x y.
Proof. by []. Qed.
