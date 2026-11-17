(** Federer (1969), 3.4.8(16), p. 337:
    if the source germ misses the regular piece,
    its containment in alpha union omega reduces to
    the exceptional germ union omega. This supporting
    Boolean connection uses only the sealed germ laws. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import SetGermUP SetGermSealed SetGermLaws SetGermOrder SetGermBooleanOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_germ_avoid_union_piece]: the displayed
    containment gamma(T) subset beta union omega in
    the proof of 3.4.8(16), p. 337. *)
Theorem set_germ_avoid_union_piece (X:topologicalType) a
    (sigma beta zeta omega:@set_germ_space X a):
  set_germ_subset sigma (@SetGerms.join X a (@SetGerms.join X a beta zeta) omega) ->
  @SetGerms.meet X a sigma zeta=@set_germ X a set0 ->
  set_germ_subset sigma (@SetGerms.join X a beta omega).
Proof.
move=>hContained hAvoid.
rewrite /set_germ_subset (set_germ_intersection_commutative sigma _)
  !set_germ_distributive (set_germ_intersection_commutative zeta sigma)
  hAvoid set_germ_union_empty in hContained.
rewrite -hContained.
apply:set_germ_subset_join_bound.
- exact:set_germ_subset_transitive (set_germ_meet_subset_left beta sigma) (set_germ_subset_join_left beta omega).
- exact:set_germ_subset_transitive (set_germ_meet_subset_left omega sigma) (set_germ_subset_join_right beta omega).
Qed.
