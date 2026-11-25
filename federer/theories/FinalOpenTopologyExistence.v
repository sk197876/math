(** Federer (1969), 4.1.1, p. 344: existence of the literal
    final topology on the union of fixed-support test-function spaces.
    This construction is kept separate from its universal-property laws. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import OpenFamilyTopologyUP FinalOpenTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section FinalTopologyExistence.
Variable J:Type.
Variable E:J->Type.
Variable X:Type.
Variable OE:forall j,set (set (E j)).
Variable inc:forall j,E j->X.
Hypothesis hE:forall j,is_open_family_topology (@OE j).

(** Source for [final_open_witness]: the open-set construction
    explicitly printed in Federer 4.1.1, p. 344: every inverse
    image under a fixed-support inclusion is open. *)
Definition final_open_witness (A:set X) :=
  forall j,@OE j [set x|A (@inc j x)].

(** Source for [final_open_topology_exists]: existence of the
    final topology in Federer 4.1.1, p. 344. Its topological
    universal property assumes no vector-space continuity. *)
Theorem final_open_topology_exists :
  exists O,is_final_open_topology OE inc O.
Proof.
exists final_open_witness; split.
- constructor.
  + move=>j; exact:open_family_whole (hE j).
  + move=>A B hA hB j.
    exact:(@open_family_intersection (E j) (@OE j) (hE j)
      [set x|A (@inc j x)] [set x|B (@inc j x)] (hA j) (hB j)).
  + move=>I A hA j.
    exact:(@open_family_union (E j) (@OE j) (hE j) I
      (fun i=>[set x|A i (@inc j x)]) (fun i=>hA i j)).
- by move=>A.
Qed.
End FinalTopologyExistence.

(** Source for [final_open_topology_unique]: supporting uniqueness
    of the literal topology in Federer 4.1.1, p. 344, from its
    open-set characterization. *)
Theorem final_open_topology_unique (J:Type) (E:J->Type) (X:Type)
    (OE:forall j,set (set (E j))) (inc:forall j,E j->X)
    (O P:set (set X)) :
  is_final_open_topology OE inc O -> is_final_open_topology OE inc P -> O = P.
Proof.
move=>hO hP; apply:funext=>A; apply:propext; split=>hA.
- apply:(hP.2 A).2; exact:(hO.2 A).1.
- apply:(hO.2 A).2; exact:(hP.2 A).1.
Qed.

(** Source for [final_open_topology_finest]: the final topology
    is the largest topology making every fixed-support inclusion
    continuous, exactly as specified in Federer 4.1.1, p. 344. *)
Theorem final_open_topology_finest (J:Type) (E:J->Type) (X:Type)
    (OE:forall j,set (set (E j))) (inc:forall j,E j->X)
    (O Q:set (set X)) :
  is_final_open_topology OE inc O ->
  (forall j,open_family_continuous (@OE j) Q (inc j)) ->
  forall A,Q A -> O A.
Proof. by move=>hO hi A hA; apply:(hO.2 A).2=>j; exact:hi. Qed.
