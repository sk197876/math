(** Federer (1969), 4.1.1, pp. 344–345: connect independently
    specified open-set topologies to the existing general-topology
    interface. This adapter imports no external distribution theory
    or locally convex vector-space theorems. *)
From HB Require Import structures.
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [open_family_topological_space]: supporting carrier
    for the specified function-space topology in Federer 4.1.1,
    p. 344. Different topologies retain different wrappers. *)
Definition open_family_topological_space (X:choiceType) (O:set (set X))
    (_:is_open_family_topology O) : Type := X.
HB.instance Definition _ (X:choiceType) (O:set (set X))
    (hO:is_open_family_topology O) :=
  Choice.copy (open_family_topological_space hO) X.

Section OpenFamilyTopologyAdapter.
Variable X:choiceType.
Variable O:set (set X).
Hypothesis hO:is_open_family_topology O.
Local Notation T := (open_family_topological_space hO).

(** Source for [open_family_adapter_whole]: the supplied
    whole-space law is the topology law required by the background
    interface, supporting Federer 4.1.1, p. 344. *)
Lemma open_family_adapter_whole : O (@setT T).
Proof. exact:open_family_whole hO. Qed.

(** Source for [open_family_adapter_intersection]: finite
    intersections retain the supplied topology, supporting
    Federer 4.1.1, p. 344. *)
Lemma open_family_adapter_intersection : setI_closed O.
Proof. exact:open_family_intersection hO. Qed.

(** Source for [open_family_adapter_union]: arbitrary unions
    retain the supplied topology, supporting Federer 4.1.1, p. 344. *)
Lemma open_family_adapter_union (I:Type) (A:I->set T) :
  (forall i,O (A i)) -> O (\bigcup_i A i).
Proof. exact:(@open_family_union X O hO I A). Qed.
HB.instance Definition _ := isOpenTopological.Build T
  open_family_adapter_whole open_family_adapter_intersection open_family_adapter_union.

(** Source for [open_family_space_open]: the background open-set
    predicate is precisely the independently specified topology;
    no topology is silently substituted, Federer 4.1.1, p. 344. *)
Lemma open_family_space_open (A:set T) :
  @open [the topologicalType of T] A <-> O A.
Proof. by []. Qed.
End OpenFamilyTopologyAdapter.

(** Source for [open_family_continuousP]: inverse-image continuity
    agrees with the background general-topology predicate, supporting
    the maps in Federer 4.1.1, pp. 344–345. *)
Theorem open_family_continuousP (X Y:choiceType)
    (OX:set (set X)) (OY:set (set Y))
    (hX:is_open_family_topology OX) (hY:is_open_family_topology OY) (f:X->Y) :
  open_family_continuous OX OY f <->
  continuous (fun x:open_family_topological_space hX=>
    (f x:open_family_topological_space hY)).
Proof.
rewrite continuousP; by [].
Qed.
