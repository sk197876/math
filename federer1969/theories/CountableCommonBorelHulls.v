(** Supporting arbitrary-target extension of the exponent limit in Federer
    (1969), 2.10.9, p. 175. Intersect countably many Borel hulls from the
    definition in 2.2.3, p. 61. This is elementary infrastructure, not a
    separately printed theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_common_borel_hull]: supporting common
    hull for the measures of a sequence of exponents in Federer
    2.10.9, p. 175, from 2.2.3, p. 61. Equalities hold
    for every index even if some values are infinite. *)
Theorem countable_common_borel_hull (R : realType) (X : topologicalType)
    (mu : nat -> set X -> \bar R) (A : set X) :
  (forall n, is_measure (mu n)) -> (forall n, is_borel_regular_measure (mu n)) ->
  exists B, A `<=` B /\ borel_set B /\ forall n, mu n A=mu n B.
Proof.
move=> hm hr.
have hex n : exists B, A `<=` B /\ borel_set B /\ mu n A=mu n B.
  exact: borel_regular_cover (hr n) A.
pose C n := projT1 (cid (hex n)).
have hC n : A `<=` C n /\ borel_set (C n) /\ mu n A=mu n (C n) := projT2 (cid (hex n)).
pose B := \bigcap_n C n.
have hAB : A `<=` B by move=> x hx n _; exact: (hC n).1 x hx.
exists B; split=> //; split.
- apply: (@borel_set_countable_intersection X nat setT C (countableP _) (ex_intro _ 0%N I))=> n _.
  exact: (hC n).2.1.
- move=> n; apply/eqP; rewrite eq_le; apply/andP; split.
  + exact: (@measure_mono R X (mu n) (hm n) A B hAB).
  + rewrite (hC n).2.2; apply: (@measure_mono R X (mu n) (hm n))=> x hx; exact: hx n I.
Qed.
