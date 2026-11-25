(** Federer (1969), 2.2.16, pp. 71–72: abstract properties of the closed
    C_n(V) refinement of an open family. These laws suffice for the Ulam
    null-union argument; the well-order and complement-distance witness are
    kept private. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_separated_closed_open_refinement]: direct
    laws used for C_n(V) in Federer 2.2.16,
    pp. 71–72: closedness, inclusion in V, countable
    exhaustion of the open union, and uniform separation
    within each fixed positive-integer level. *)
Record is_separated_closed_open_refinement (R : realType) (X : metricType R)
    (J : Type) (D : set J) (U : J -> set X) (C : nat -> J -> set X) : Prop := {
  closed_open_refinement_closed : forall n j, D j -> closed (C n j);
  closed_open_refinement_inside : forall n j, D j -> C n j `<=` U j;
  closed_open_refinement_cover : (\bigcup_(j in D) U j) = \bigcup_n \bigcup_(j in D) C n j;
  closed_open_refinement_separated : forall n j k, D j -> D k -> j <> k ->
    forall x y, C n j x -> C n k y -> ((n.+1)%:R)^-1 <= mdist x y
}.
