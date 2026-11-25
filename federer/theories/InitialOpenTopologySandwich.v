(** Federer (1969), 4.1.1, p. 344: E(U,Y) and D(U,Y)
    induce the same topology on each D_K(U,Y). This supporting
    general-topology lemma states the exact sandwich argument. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import OpenFamilyTopologyUP InitialOpenTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [initial_open_topology_sandwich]: equality of the
    two induced step topologies in Federer 4.1.1, p. 344, follows
    from continuous step inclusion and continuous D-to-E inclusion.
    No vector-topology hypothesis is used. *)
Theorem initial_open_topology_sandwich (W D E:Type)
    (P:set (set W)) (S:set (set D)) (O:set (set E))
    (j:W->D) (inc:D->E) (k:W->E) :
  is_initial_open_topology O k P ->
  open_family_continuous P S j -> open_family_continuous S O inc ->
  (forall w,inc (j w)=k w) -> is_initial_open_topology S j P.
Proof.
move=>hP hj hInc he; split; first exact:hP.1.
move=>B; split.
- move=>hB; have [A [hA hEq]]:=(hP.2 B).1 hB.
  exists [set d|A (inc d)]; split; first exact:hInc A hA.
  rewrite hEq; apply:funext=>w; by rewrite /= he.
- move=>[A [hA ->]]; exact:hj A hA.
Qed.
