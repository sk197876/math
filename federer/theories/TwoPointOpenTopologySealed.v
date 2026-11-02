(** Sealed finite-topology witness for the local test of
    Federer (1969), 2.10.1, p. 170. Only the carrier,
    two points and the abstract open-set laws are exposed.
    Source context and edition comparisons: TwoPointOpenTopologyUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import TwoPointOpenTopologyUP TwoPointOpenTopologyConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type TwoPointOpenTopologySignature.
(** Source for [space]: abstract carrier of the finite
    topological test supporting Federer 2.10.1, p. 170. *)
Parameter space : topologicalType.
(** Source for [first]: first point of the abstract topology
    used to test Federer 2.10.1, p. 170. *)
Parameter first : space.
(** Source for [second]: second point of the abstract topology
    used to test Federer 2.10.1, p. 170. *)
Parameter second : space.
(** Source for [laws]: only the proved open-set specification
    for the local test of Federer 2.10.1, p. 170. *)
Parameter laws : is_two_point_open_topology first second.
End TwoPointOpenTopologySignature.

Module TwoPointOpenTopology : TwoPointOpenTopologySignature.
Section Selection.
(** Source for [witness]: private use of the proved existence
    of the test space supporting Federer 2.10.1, p. 170. *)
Let witness := cid two_point_open_topology_exists.
(** Source for [space]: carrier of the proved finite-topology
    witness supporting Federer 2.10.1, p. 170. *)
Definition space : topologicalType := projT1 witness.
(** Source for [points]: private point-pair witness for the
    local topological test of Federer 2.10.1, p. 170. *)
Let points := cid (projT2 witness).
(** Source for [first]: first point of the proved witness
    supporting Federer 2.10.1, p. 170. *)
Definition first : space := (projT1 points).1.
(** Source for [second]: second point of the proved witness
    supporting Federer 2.10.1, p. 170. *)
Definition second : space := (projT1 points).2.
(** Source for [laws]: expose the proved abstract topology
    laws for the local test of Federer 2.10.1, p. 170. *)
Lemma laws : is_two_point_open_topology first second.
Proof. exact: projT2 points. Qed.
End Selection.
End TwoPointOpenTopology.
