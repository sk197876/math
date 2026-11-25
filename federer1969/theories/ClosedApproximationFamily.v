(** Federer (1969), 2.2.2, p. 61: the class F of closed-approximable sets
    satisfies (2),(3) of 2.2.1 and contains all closed sets. Sequence
    arguments are transferred to arbitrary countable families; nonempty
    intersections use enumeration without empty gaps. Source context:
    ClosedApproximationUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP CountablyClosedFamilyUP CountableFamilySequence
  CountableFamilyEnumeration ClosedApproximationUP ClosedApproximationIntersection
  ClosedApproximationUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [closed_approximable_countably_closed]: Federer
    2.2.2, p. 61, conclusion after the two displayed estimates:
    the approximation class has both countable closure properties.
    Finiteness of the total measure is used only for union closure. *)
Theorem closed_approximable_countably_closed (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) : mu setT < +oo ->
  (forall K, closed K -> measure_measurable mu K) ->
  is_countably_closed_family false setT (is_closed_approximable mu).
Proof.
move=> hf hc; constructor.
- exact: (@closed_set_approximable R T mu hm set0 closed0).
- by move=> A _ x _.
- move=> G hG hGc _.
  have [A [hA he]] := @countable_family_as_sequence _ _ G (fun A => A) hGc.
  rewrite -he; apply: (@closed_approximable_sequence_union R T mu hm A hf hc).
  move=> n; have [h0|[B [hB hEq]]] := hA n.
  + rewrite h0; exact: (@closed_set_approximable R T mu hm set0 closed0).
  + rewrite hEq; exact: hG B hB.
- move=> G hG hGc hn.
  have [A [hA he]] := @countable_nonempty_intersection_sequence _ _ G (fun A => A) hGc hn.
  rewrite -he; apply: (@closed_approximable_sequence_intersection R T mu hm A).
  move=> n; have [B [hB hEq]] := hA n; rewrite hEq; exact: hG B hB.
Qed.
