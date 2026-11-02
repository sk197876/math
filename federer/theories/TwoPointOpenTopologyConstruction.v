(** Private finite witness for the abstract topology supporting the local
    test of Federer (1969), 2.10.1, p. 170. This is a general-topology
    existence construction, not a claim that the book. Source context and
    edition comparisons: TwoPointOpenTopologyUP.v. Downstream proofs use
    only the sealed topology laws. *)
From HB Require Import structures.
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import TwoPointOpenTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [two_point_open_carrier_witness]: private finite
    carrier for the test of Federer 2.10.1, p. 170.
    A wrapper keeps its topology separate from discrete bool. *)
Definition two_point_open_carrier_witness : Type := bool.
HB.instance Definition _ := Choice.copy two_point_open_carrier_witness bool.

(** Source for [two_point_open_sets_witness]: private open-set
    laws for the finite test space supporting Federer 2.10.1,
    p. 170: the open sets are empty, the second singleton,
    and the whole space. *)
Definition two_point_open_sets_witness (U : set two_point_open_carrier_witness) :=
  U false -> U true.

(** Source for [two_point_open_whole_witness]: supporting
    whole-space topology law for the local test of Federer
    2.10.1, p. 170. *)
Lemma two_point_open_whole_witness : two_point_open_sets_witness setT.
Proof. by []. Qed.

(** Source for [two_point_open_intersection_witness]: supporting
    finite-intersection topology law for the local test of
    Federer 2.10.1, p. 170. *)
Lemma two_point_open_intersection_witness : setI_closed two_point_open_sets_witness.
Proof. by move=> A B hA hB [hAf hBf]; split; [exact: hA|exact: hB]. Qed.

(** Source for [two_point_open_union_witness]: supporting
    arbitrary-union topology law for the local test of Federer
    2.10.1, p. 170. No countability restriction is used. *)
Lemma two_point_open_union_witness (I : Type) (f : I -> set two_point_open_carrier_witness) :
  (forall i, two_point_open_sets_witness (f i)) ->
  two_point_open_sets_witness (\bigcup_i f i).
Proof. move=> hF [i _ hi]; exists i=> //; exact: hF i hi. Qed.

HB.instance Definition _ := isOpenTopological.Build two_point_open_carrier_witness
  two_point_open_whole_witness two_point_open_intersection_witness two_point_open_union_witness.

(** Source for [two_point_open_topology_exists]: proved finite
    witness for the abstract topological test of Federer
    2.10.1, p. 170. Construct only the topology laws here;
    the open-refinement conclusions are derived from the
    abstract specification in separate public proofs. *)
Theorem two_point_open_topology_exists : exists X : topologicalType,
  exists pq : X*X, is_two_point_open_topology pq.1 pq.2.
Proof.
exists [the topologicalType of two_point_open_carrier_witness],(false,true).
split; first by [].
split; first by case=> [|]; [right|left].
by move=> U.
Qed.
