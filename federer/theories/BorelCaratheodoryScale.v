(** Supporting normalization of the exponent limit in Federer (1969),
    2.10.9, p. 175. A positive finite constant multiplying every Borel cost
    multiplies the independently constructed measure by that constant,
    including infinite values. This follows from the covering laws in
    2.10.1, p. 170, and the weighted comparison already used for 2.10.5, p.
    173. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumScale BorelCoverCostUP
  BorelCaratheodoryMeasure CaratheodoryWeightedComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_cover_cost_scale]: supporting finite
    nonnegative rescaling of the cost hypothesis in Federer
    2.10.8, used by 2.10.9, p. 175. The scalar-zero case
    retains the book's zero-times-infinity convention. *)
Lemma borel_cover_cost_scale (R : realType) (X : topologicalType)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c) (a : R) :
  (0<=a)%R -> is_borel_cover_cost (fun B => a%:E*c B).
Proof.
move=> ha; constructor.
- move=> B hB; apply: mule_ge0; first exact ha.
  exact: (@borel_cover_cost_nonnegative R X c hc B hB).
- move=> J D S A hD hA hS hcov.
  rewrite nonnegative_sum_scale //; last first.
    move=> j hj; exact: (@borel_cover_cost_nonnegative R X c hc (S j) (hS j hj)).
  apply: lee_wpmul2l; first exact ha.
  exact: (@borel_cover_cost_cover R X c hc J D S A hD hA hS hcov).
Qed.

(** Source for [borel_caratheodory_positive_scale]: supporting
    normalization identity for the limit assertion in Federer
    2.10.9, p. 175, from the abstract construction 2.10.1,
    p. 170. Both sides are independently defined set functions. *)
Theorem borel_caratheodory_positive_scale (R : realType) (X : metricType R)
    (c : set X -> \bar R) (hc : is_borel_cover_cost c) (a : R) :
  (0<a)%R -> forall A, borel_caratheodory_measure (fun B => a%:E*c B) A=
    a%:E*borel_caratheodory_measure c A.
Proof.
move=> ha A.
have hd := @borel_cover_cost_scale R X c hc a (ltW ha).
pose J := @borel_metric_sets R X.
pose S (j : J) := val j.
pose C (j : J) := c (val j).
pose D (j : J) := a%:E*c (val j).
have hC j : 0<=C j := @borel_cover_cost_nonnegative R X c hc (val j) (set_valP j).
have hD j : 0<=D j := @borel_cover_cost_nonnegative R X _ hd (val j) (set_valP j).
have hlo := @caratheodory_normalized_cost_comparison R X J S C D
  (borel_caratheodory_measure c) (borel_caratheodory_measure (fun B => a%:E*c B)) a 1
  (borel_caratheodory_specification c) (borel_caratheodory_specification (fun B => a%:E*c B))
  hC hD ha ltr01 (fun j => ltac:(by rewrite /C /D mul1e)) A.
have hup := @caratheodory_normalized_cost_comparison R X J S D C
  (borel_caratheodory_measure (fun B => a%:E*c B)) (borel_caratheodory_measure c) 1 a
  (borel_caratheodory_specification (fun B => a%:E*c B)) (borel_caratheodory_specification c)
  hD hC ltr01 ha (fun j => ltac:(by rewrite /C /D mul1e)) A.
move: hlo hup; rewrite !mul1e=> hlo hup; by apply/eqP; rewrite eq_le hup hlo.
Qed.
