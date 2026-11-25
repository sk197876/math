(** Federer (1969), 2.10.40, printed p. 200: nested nonempty compact
    feasible-centre sets have nonempty intersection. This supporting
    countable form uses the project's finite-cover compactness argument;
    only the first set need be compact if all sets are closed and decrease. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
From Federer Require Import CompactDecreasingNeighborhoods.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_nested_nonempty_intersection]: supporting
    compact intersection step in 2.10.40, p. 200.
    The topology is arbitrary; nonemptiness of the
    intersection is proved rather than assumed. *)
Theorem compact_nested_nonempty_intersection (X : topologicalType) (C : nat -> set X) :
  compact (C 0%N) -> (forall n, closed (C n)) ->
  (forall n m, (n<=m)%N -> C m `<=` C n) ->
  (forall n, C n !=set0) -> (\bigcap_n C n) !=set0.
Proof.
move=> hc hclosed hdec hne.
apply: contrapT=> hnone.
have hsub : (\bigcap_n C n) `<=` set0.
  move=> x hx; apply: hnone; by exists x.
have [N hN] := @compact_decreasing_eventually_in_open X C set0 hc hclosed hdec open0 hsub.
have [x hx] := hne N.
exact: hN N (leqnn N) x hx.
Qed.
