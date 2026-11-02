(** Federer (1969), 2.2.10(2), p. 67: the Borel sets B(s) contain f(C
    intersect A(s)), are disjoint among siblings, and lie inside both their
    parent and the closure of f(C intersect E(s)). The root B(empty) is the
    whole TARGET Y. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot classical_sets topology.
From Federer Require Import TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_borel_image_tree]: abstract laws of B(s) in Federer
    2.2.10(2), p. 67. The closure bound is required only away from the root,
    whose value is all of Y. Later proofs use these laws without unfolding
    the recursive separator choices. *)
Record is_borel_image_tree (X : Type) (Y : topologicalType) (f : X -> Y)
    (C : set X) (E A : seq nat -> set X) (B : seq nat -> set Y) : Prop := {
  borel_image_tree_root : B [::] = setT;
  borel_image_tree_borel : forall s, borel_set (B s);
  borel_image_tree_contains : forall s, (f @` (C `&` A s)) `<=` B s;
  borel_image_tree_child_subset : forall s j, B (j::s) `<=` B s;
  borel_image_tree_children_disjoint : forall s i j,
    i <> j -> B (i::s) `&` B (j::s) = set0;
  borel_image_tree_closure_bound : forall s, s <> [::] ->
    B s `<=` closure (f @` (C `&` E s))
}.
