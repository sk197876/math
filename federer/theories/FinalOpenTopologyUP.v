(** Federer (1969), 4.1.1, p. 344: D(U,Y) has the largest
    topology making every fixed-support inclusion continuous.
    This is a final topology in topological spaces. No compatibility
    with vector operations or local convexity is asserted here. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_final_open_topology]: the literal open-set
    characterization of D(U,Y) in Federer 4.1.1, p. 344. It is
    distinct from the locally convex inductive-limit specification
    in Menne (2016), Definition 2.13 and Remark 2.17, p. 996. *)
Definition is_final_open_topology (J : Type) (E : J -> Type) (X : Type)
    (OE : forall j,set (set (E j))) (inc : forall j,E j->X)
    (O : set (set X)) :=
  is_open_family_topology O /\ forall A,
    O A <-> forall j, OE j [set x | A (inc j x)].

(** Source for [final_open_topology_inclusion]: each fixed-support
    inclusion is continuous for the topology printed in Federer
    4.1.1, p. 344. *)
Lemma final_open_topology_inclusion (J : Type) (E : J -> Type) (X : Type)
    (OE : forall j,set (set (E j))) (inc : forall j,E j->X)
    (O : set (set X)) :
  is_final_open_topology OE inc O ->
  forall j,open_family_continuous (OE j) O (inc j).
Proof. by move=>hO j A hA; exact: (hO.2 A).1 hA j. Qed.

(** Source for [final_open_topology_mapping]: a map out of the
    literal final topology is continuous exactly when all its
    fixed-support restrictions are continuous, supporting Federer
    4.1.1, pp. 344–345. No linearity is needed in this topology. *)
Theorem final_open_topology_mapping (J : Type) (E : J -> Type) (X Y : Type)
    (OE : forall j,set (set (E j))) (inc : forall j,E j->X)
    (O : set (set X)) (OY : set (set Y)) (f:X->Y) :
  is_final_open_topology OE inc O ->
  (open_family_continuous O OY f <->
   forall j,open_family_continuous (OE j) OY (fun x=>f (inc j x))).
Proof.
move=>hO; split=>hf.
- move=>j; exact:open_family_continuous_compose (final_open_topology_inclusion hO j) hf.
- move=>A hA; apply:(hO.2 _).2=>j; exact:hf j A hA.
Qed.
