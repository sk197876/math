(** Domain and sign facts for Federer (1969), 2.10.18, p. 180. Its strict
    cost growth ensures positive finite denominators, so the original
    partial quotient has a fine domain and its nonnegative limits are
    ordered. No convention change is needed here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivates ExtendedRealConventions
  PartialFunctionUP CoveringRelationUP CoveringRelationFineness CoveringRelationLimits
  CaratheodoryDensityUpperBound CaratheodoryEnlargementUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [caratheodory_positive_cost_limits]: supporting
    sign and ordered-limit assertions for 2.10.18(2)–(3),
    pp. 180–181. Fineness is checked on the actual
    quotient domain rather than assumed from C alone. *)
Lemma caratheodory_positive_cost_limits (R : realType) (X : metricType R)
    (F : set (set X)) (c mu : set X -> \bar R)
    (E : set X -> set X) (k : R) x :
  is_caratheodory_enlargement F c E k -> is_measure mu ->
  covering_relation_fine_at (caratheodory_family_relation F) x ->
  0<=covering_lower_limit (caratheodory_family_relation F) (measure_ratio_function mu c) x /\
  covering_lower_limit (caratheodory_family_relation F) (measure_ratio_function mu c) x<=
  covering_upper_limit (caratheodory_family_relation F) (measure_ratio_function mu c) x.
Proof.
move=> hE hm hf.
have hdomain : covering_relation_fine_at (fun x S => caratheodory_family_relation F x S /\
    partial_function_domain (measure_ratio_function mu c) S) x.
  apply: (covering_relation_fine_iff_small_diameter _ x).2=> e he.
  have [S [hS hd]] := (covering_relation_fine_iff_small_diameter _ x).1 hf e he.
  have hp := @caratheodory_enlargement_cost_positive R X F c E k hE S hS.1.
  have hc := @caratheodory_enlargement_cost_finite R X F c E k hE S hS.1.
  have hfin : c S \is a fin_num by rewrite (ge0_fin_numE (ltW hp)).
  exists S; split=> //; split=> //; exists (mu S/c S).
  exact: measure_ratio_positive_finite_denominator hp hfin.
split; last exact: covering_limits_ordered hdomain.
apply: le_trans _ (@covering_lower_limit_ge_level R X (caratheodory_family_relation F)
  (measure_ratio_function mu c) x 1%R (@ltr01 R)).
apply: extended_real_inf_greatest=> y [S [[hF _] [_ hy]]].
move: hy; rewrite /measure_ratio_function /= /extended_divide.
case: ifP=> // _ [<-]; apply: mule_ge0; first exact: (@measure_nonnegative R X mu hm S).
rewrite inve_ge0; exact: ltW (@caratheodory_enlargement_cost_positive R X F c E k hE S hF).
Qed.
