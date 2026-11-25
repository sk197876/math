(** Federer (1969), proof of 2.4.4(2), p. 83: geometric step quantisation,
    specified by its cell values. The function is zero on nonpositive inputs
    and takes the lower endpoint on each positive cell [t^j,t^(j+1)). Source
    editions: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_geometric_quantisation]: abstract specification
    of the geometric approximant used in Federer 2.4.4(2),
    p. 83. This predicate introduces no project axiom. *)
Definition is_geometric_quantisation (R : realType) (t : R) (q : R -> R) : Prop :=
  (forall x, x <= 0 -> q x = 0) /\
  (forall x, 0 < x -> exists j : int, t^j <= x /\ x < t^(j+1) /\ q x = t^j).
