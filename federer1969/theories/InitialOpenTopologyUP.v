(** Federer (1969), 4.1.1, p. 344: independently specify the
    topology induced on a fixed-support space by its inclusion
    into E(U,Y). *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import OpenFamilyTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_initial_open_topology]: the relative topology
    under an injective inclusion, as used for D_K(U,Y) in
    Federer 4.1.1, p. 344. The same specification also allows an
    arbitrary map and its initial topology. *)
Definition is_initial_open_topology (X Y:Type) (O:set (set Y))
    (inc:X->Y) (P:set (set X)) :=
  is_open_family_topology P /\ forall B,P B <-> exists A,
    O A /\ B=[set x|A (inc x)].

(** Source for [initial_open_topology_inclusion]: continuity of
    the inclusion with its induced topology, supporting Federer
    4.1.1, p. 344. *)
Lemma initial_open_topology_inclusion (X Y:Type) (O:set (set Y))
    (inc:X->Y) (P:set (set X)) :
  is_initial_open_topology O inc P -> open_family_continuous P O inc.
Proof. move=>hP A hA; apply:(hP.2 _).2; by exists A. Qed.

(** Source for [initial_open_topology_mapping]: a map into the
    induced topology is continuous exactly when its composition
    with the inclusion is continuous, supporting the fixed-support
    topology assertions in Federer 4.1.1, pp. 344–345. *)
Theorem initial_open_topology_mapping (X Y Z:Type)
    (O:set (set Y)) (inc:X->Y) (P:set (set X))
    (Q:set (set Z)) (f:Z->X) :
  is_initial_open_topology O inc P ->
  (open_family_continuous Q P f <->
    open_family_continuous Q O (fun z=>inc (f z))).
Proof.
move=>hP; split.
- move=>hf; exact:open_family_continuous_compose hf (initial_open_topology_inclusion hP).
- move=>hf B /(hP.2 B).1 [A [hA ->]]; exact:hf A hA.
Qed.
