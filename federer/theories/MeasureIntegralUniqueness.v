(** Supporting order consequences of the integral definitions in Federer
    (1969), 2.4.2, p. 81. Source context: MeasureIntegralUP.v. These facts
    use the abstract specifications alone, before any choice of integral
    values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_upper_integral_unique]: uniqueness of
    the infimum defining the upper integral in Federer 2.4.2, p. 81. *)
Lemma measure_upper_integral_unique (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) a b :
  is_measure_upper_integral mu f a -> is_measure_upper_integral mu f b -> a=b.
Proof.
move=> ha hb; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: hb.2 a ha.1.
- exact: ha.2 b hb.1.
Qed.

(** Source for [measure_lower_integral_unique]: uniqueness of
    the supremum defining the lower integral in Federer 2.4.2, p. 81. *)
Lemma measure_lower_integral_unique (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) a b :
  is_measure_lower_integral mu f a -> is_measure_lower_integral mu f b -> a=b.
Proof.
move=> ha hb; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: ha.2 b hb.1.
- exact: hb.2 a ha.1.
Qed.

(** Source for [measure_integral_unique]: the common integral
    value is unique in Federer 2.4.2, p. 81. *)
Lemma measure_integral_unique (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) a b :
  is_measure_integral mu f a -> is_measure_integral mu f b -> a=b.
Proof. move=> ha hb; exact: measure_upper_integral_unique ha.2.1 hb.2.1. Qed.

(** Source for [measure_summable_integrable]: summability implies
    integrability by definition, Federer 2.4.2, p. 81, final sentence. *)
Lemma measure_summable_integrable (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (f : partial_function X (extended_real_line R)) :
  is_measure_summable mu f -> is_measure_integrable mu f.
Proof. move=> [a ha]; by exists a%:E. Qed.
