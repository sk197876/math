(** Federer (1969), 2.4.9, p. 85: a summable dominating function is finite
    almost everywhere, permitting the finite scalar calculations in the
    proof. This follows from 2.4.4(8), p. 82, and 2.4.3(4), p. 82, applied
    to its absolute value. Source context: MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci PartialAbsolutePartsGraph MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureIntegralAbsolute MeasureUpperIntegralPositivePart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_finite_locus]: supporting finite-
    value region for the dominated calculations in Federer
    2.4.9, p. 85; the partial value must exist. *)
Definition partial_extended_finite_locus (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :=
  [set x | exists y, partial_function_graph f x y /\ y \is a fin_num].

(** Source for [measure_summable_finite_almost]: supporting
    almost-everywhere finiteness of the dominating function in
    Federer 2.4.9, p. 85, from the preceding integral laws. *)
Lemma measure_summable_finite_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_summable mu f -> measure_almost_everywhere mu (partial_extended_finite_locus f).
Proof.
move=> hf; have [b hb] := @measure_summable_absolute_value R X mu hm f hf.
have he := @measure_upper_integral_unique R X mu _ _ b%:E (measure_upper_integral_specification mu _) hb.2.1.
have hfin : measure_upper_integral mu (partial_extended_function_absolute_value f) < +oo by rewrite he ltry.
have h := (@measure_finite_upper_integral_consequences R X mu hm _ hfin).2.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ h)=> x [y [[z [hz ezy]] hy]].
exists z; split=> //; by rewrite fin_num_abs ezy.
Qed.
