(** Federer (1969), 4.1.1, p. 344: opaque literal final
    topology. Only the independently specified inverse-image
    open-set characterization is exposed. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import OpenFamilyTopologyUP FinalOpenTopologyUP FinalOpenTopologyExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FinalOpenTopologySignature.
(** Source for [opens]: the largest topology making all the
    original step inclusions continuous, Federer 4.1.1, p. 344. *)
Parameter opens:forall (J:Type) (E:J->Type) (X:Type)
    (OE:forall j,set (set (E j))) (inc:forall j,E j->X),
  (forall j,is_open_family_topology (@OE j))->set (set X).
(** Source for [laws]: openness is exactly openness on every
    fixed-support step, Federer 4.1.1, p. 344. *)
Parameter laws:forall (J:Type) (E:J->Type) (X:Type)
    (OE:forall j,set (set (E j))) (inc:forall j,E j->X)
    (hE:forall j,is_open_family_topology (@OE j)),
  is_final_open_topology OE inc (@opens J E X OE inc hE).
End FinalOpenTopologySignature.
Module FinalOpenTopology:FinalOpenTopologySignature.
(** Source for [opens]: select the already proved final-topology
    witness, supporting Federer 4.1.1, p. 344. *)
Definition opens (J:Type) (E:J->Type) (X:Type)
    (OE:forall j,set (set (E j))) (inc:forall j,E j->X)
    (hE:forall j,is_open_family_topology (@OE j)):set (set X):=
  projT1 (cid (final_open_topology_exists inc hE)).
(** Source for [laws]: the selected witness has exactly the
    printed open-set laws, Federer 4.1.1, p. 344. *)
Lemma laws (J:Type) (E:J->Type) (X:Type)
    (OE:forall j,set (set (E j))) (inc:forall j,E j->X)
    (hE:forall j,is_open_family_topology (@OE j)):
  is_final_open_topology OE inc (@opens J E X OE inc hE).
Proof. exact:(projT2 (cid (final_open_topology_exists inc hE))). Qed.
End FinalOpenTopology.
