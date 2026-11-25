(** Federer (1969), 2.4.4(6), p. 82, proof p. 83: integrability is
    equivalent to existence of the difference between the two part
    integrals, and the difference is the integral. Source context:
    MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialExtendedArithmetic
  MeasureUP MeasurableFunctionUP PartialFunctionIntegralParts MeasureUpperIntegralPositivePart MeasureIntegralNegation
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureBoundGraphEquivalence MeasureIntegralNegationLaw MeasureIntegralAddition MeasureIntegralPartsExist NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral_from_parts]: the forward
    construction in Federer 2.4.4(6), proof p. 83:
    a defined difference of part integrals is the integral of f. *)
Lemma measure_integral_from_parts (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) P N a :
  is_measure_integral mu (partial_extended_function_positive_part f) P ->
  is_measure_integral mu (partial_extended_function_negative_part f) N ->
  extended_subtract P N=Some a -> is_measure_integral mu f a.
Proof.
move=> hp hn ha; have hneg := @measure_integral_negation R X mu hm _ N hn.
have hsum := @measure_integral_add R X mu hm _ _ P (-N) a hp hneg ha.
exact: measure_integral_graph_equivalent (partial_parts_difference_graph f) hsum.
Qed.

(** Source for [integrable_function_part_difference_defined]:
    converse definedness argument in Federer 2.4.4(6),
    proof p. 83. At least one part integral is finite,
    by 2.4.3(4) applied to f or -f. *)
Lemma integrable_function_part_difference_defined (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a P N :
  is_measure_integral mu f a ->
  is_measure_integral mu (partial_extended_function_positive_part f) P ->
  is_measure_integral mu (partial_extended_function_negative_part f) N ->
  0 <= P -> 0 <= N -> exists z, extended_subtract P N=Some z.
Proof.
move=> hf hp hn hP hN.
have ef := @measure_upper_integral_unique R X mu f _ a (measure_upper_integral_specification mu f) hf.2.1.
have ep := @measure_upper_integral_unique R X mu _ _ P (measure_upper_integral_specification mu _) hp.2.1.
have en := @measure_upper_integral_unique R X mu _ _ N (measure_upper_integral_specification mu _) hn.2.1.
apply: (proj2 (nonnegative_difference_defined hP hN)); apply/orP.
have [ha|ha] := ltP a +oo.
- left; rewrite -ep; apply: (@measure_upper_integral_positive_part_finite R X mu hm f).
  by rewrite ef.
- right; have ea : a=+oo by apply/eqP; rewrite -leye_eq.
  have hneg := @measure_integral_negation R X mu hm f a hf.
  have ene := @measure_upper_integral_unique R X mu _ _ (-a)
    (measure_upper_integral_specification mu _) hneg.2.1.
  have hfin : measure_upper_integral mu (partial_extended_function_negate f) < +oo.
    by rewrite ene ea.
  have hpfin := @measure_upper_integral_positive_part_finite R X mu hm _ hfin.
  rewrite (@measure_upper_integral_graph_equivalent R X mu _ _ (partial_negative_part_negation_graph f)) en in hpfin.
  exact hpfin.
Qed.

(** Source for [measure_integral_parts_iff]: complete domain-
    sensitive equality in Federer 2.4.4(6), p. 82;
    neither side is assigned a default for infinity minus infinity. *)
Theorem measure_integral_parts_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a :
  is_measure_integral mu f a <-> exists P N,
    is_measure_integral mu (partial_extended_function_positive_part f) P /\
    is_measure_integral mu (partial_extended_function_negative_part f) N /\ extended_subtract P N=Some a.
Proof.
split.
- move=> hf; have [P [N [hp [hn [hP hN]]]]] := @measurable_function_parts_integrals R X mu hm f hf.1.
  have [z hz] := @integrable_function_part_difference_defined R X mu hm f a P N hf hp hn hP hN.
  have hi := @measure_integral_from_parts R X mu hm f P N z hp hn hz.
  have he := measure_integral_unique hi hf.
  exists P,N; split=> //; split=> //; by rewrite -he.
- move=> [P [N [hp [hn ha]]]]; exact (@measure_integral_from_parts R X mu hm f P N a hp hn ha).
Qed.
