(** Federer (1969), 2.4.4(3), p. 82, proof p. 83: negation preserves
    integrability and negates the integral. Source context:
    MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasurableExtendedParts MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralBounds
  MeasureIntegralNegation MeasureIntegralGraphEquivalence MeasureIntegralSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_double_negation_graph]: the
    involution used in Federer 2.4.4(3), p. 83;
    neither infinite values nor partial domains cause an exception. *)
Lemma partial_extended_double_negation_graph (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) x y :
  partial_function_graph (partial_extended_function_negate (partial_extended_function_negate f)) x y <->
  partial_function_graph f x y.
Proof.
split.
- move=> [z [[w [hw hz]] hy]]; rewrite -hz oppeK in hy; by rewrite -hy.
- move=> hy; exists (-y); split; last exact: oppeK.
  exists y; by split.
Qed.

(** Source for [double_negation_upper_integral]: supporting
    upper-bound identity in the negation argument of Federer
    2.4.4(3), p. 83. *)
Lemma double_negation_upper_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  measure_upper_integral mu (partial_extended_function_negate (partial_extended_function_negate f)) =
    measure_upper_integral mu f.
Proof.
have [he _] := @measure_step_value_families_graph_equivalent R X mu _ f
  (partial_extended_double_negation_graph f).
apply: (@measure_upper_integral_unique R X mu f).
- have h := measure_upper_integral_specification mu
    (partial_extended_function_negate (partial_extended_function_negate f)).
  by rewrite /is_measure_upper_integral he in h.
- exact: measure_upper_integral_specification.
Qed.

(** Source for [measure_integral_negation]: negation case of
    Federer 2.4.4(3), p. 82, including both infinite
    values and the integrability assertion. *)
Theorem measure_integral_negation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a :
  is_measure_integral mu f a -> is_measure_integral mu (partial_extended_function_negate f) (-a).
Proof.
move=> [hf [hu hl]].
have eu := @measure_upper_integral_unique R X mu f _ a (measure_upper_integral_specification mu f) hu.
have el := @measure_lower_integral_unique R X mu f _ a (measure_lower_integral_specification mu f) hl.
have hn := @measure_lower_integral_negation R X mu hm f.
have en : measure_upper_integral mu (partial_extended_function_negate f) = -a.
  by rewrite -el hn oppeK.
apply: (@measure_integral_squeeze R X mu hm _ (-a)).
- exact: measurable_extended_negation hf.
- by rewrite en.
- by rewrite (@measure_lower_integral_negation R X mu hm) double_negation_upper_integral eu.
Qed.

(** Source for [measure_integral_negation_iff]: the equivalence implicit in
    Federer 2.4.4(3), pp. 82–83, stated. *)
Lemma measure_integral_negation_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a :
  is_measure_integral mu (partial_extended_function_negate f) (-a) <-> is_measure_integral mu f a.
Proof.
split; last exact: measure_integral_negation.
move=> hf; have h := @measure_integral_negation R X mu hm _ (-a) hf.
rewrite oppeK in h.
exact: measure_integral_graph_equivalent (partial_extended_double_negation_graph f) h.
Qed.
