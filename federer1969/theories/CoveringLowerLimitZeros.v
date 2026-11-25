(** Federer (1969), 2.9.16, p. 161: the counterexample using all closed
    balls containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP CoveringRelationUP CoveringRelationLimits
  MetricDiameter ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [covering_lower_limit_zero_of_small_zero_values]: supporting
    lower-limit criterion for Federer 2.9.16, p. 161 Every compared value is
    nonnegative, and an actual zero graph value is available at every
    positive scale. *)
Lemma covering_lower_limit_zero_of_small_zero_values (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f : partial_function (set X) (\bar R)) x :
  (forall S y, V x S -> partial_function_graph f S y -> 0<=y) ->
  (forall e : R, (0<e)%R -> exists S,
    V x S /\ extended_metric_diameter S<e%:E /\ partial_function_graph f S 0) ->
  covering_lower_limit V f x=0.
Proof.
move=> hnon hzero; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_sup_least=> b [e [he ->]].
  have [S [hS [hdiam hf]]] := hzero e he.
  apply: extended_real_inf_lower; by exists S; split=> //; split.
- apply: le_trans _ (@covering_lower_limit_ge_level R X V f x 1%R (ltr01)).
  apply: extended_real_inf_greatest=> y [S [hS [_ hy]]]; exact: hnon S y hS hy.
Qed.
