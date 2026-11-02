(** Federer (1969), 2.4.4(7)–(8), p. 82, proof p. 83: |integral f|<=integral
    |f| and summability of |f| when f is summable. Follow the displayed
    identity integral |f|=integral f++integral f- and compare it with the
    part-difference formula. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealAddVariations NumericalSumValues ExtendedRealOrderTopology
  PartialFunctionUP MeasureUP MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureIntegralAddition PartialFunctionIntegralParts PartialAbsolutePartsGraph MeasureUpperIntegralPositivePart
  MeasureIntegralPartsExist MeasureIntegralPartsDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_absolute_integral_parts_sum]: the
    displayed identity in the last proof paragraph of Federer
    2.4.4, p. 83; the sum of the nonnegative part
    integrals is always defined, possibly positive infinity. *)
Lemma measure_absolute_integral_parts_sum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) P N :
  is_measure_integral mu (partial_extended_function_positive_part f) P ->
  is_measure_integral mu (partial_extended_function_negative_part f) N ->
  0 <= P -> 0 <= N -> is_measure_integral mu (partial_extended_function_absolute_value f) (P+N).
Proof.
move=> hp hn hP hN.
have hadd : extended_add P N=Some (P+N) by rewrite /extended_add ge0_adde_def.
have hi := @measure_integral_add R X mu hm _ _ P N (P+N) hp hn hadd.
exact: measure_integral_graph_equivalent (partial_absolute_parts_graph f) hi.
Qed.

(** Source for [measure_integral_absolute_bound]: complete
    Federer 2.4.4(7), p. 82, explicitly including
    integrability of |f| and allowing its integral to be infinite. *)
Theorem measure_integral_absolute_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) a :
  is_measure_integral mu f a -> exists b,
  is_measure_integral mu (partial_extended_function_absolute_value f) b /\ `|a| <= b.
Proof.
move=> hf; have [P [N [hp [hn [hP hN]]]]] := @measurable_function_parts_integrals R X mu hm f hf.1.
have [z hz] := @integrable_function_part_difference_defined R X mu hm f a P N hf hp hn hP hN.
have hi := @measure_integral_from_parts R X mu hm f P N z hp hn hz.
have he := measure_integral_unique hi hf.
have hval : P-N=a by rewrite (extended_subtract_value hz) he.
exists (P+N); split.
- exact (@measure_absolute_integral_parts_sum R X mu hm f P N hp hn hP hN).
- rewrite -hval; have h := lee_abs_sub P N.
  by rewrite (gee0_abs hP) (gee0_abs hN) in h.
Qed.

(** Source for [measure_summable_absolute_value]: complete
    Federer 2.4.4(8), p. 82. A finite signed integral
    forces both nonnegative variations finite, hence their sum,
    the absolute-value integral, is finite. *)
Theorem measure_summable_absolute_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  is_measure_summable mu f -> is_measure_summable mu (partial_extended_function_absolute_value f).
Proof.
move=> [a hf]; have [P [N [hp [hn [hP hN]]]]] := @measurable_function_parts_integrals R X mu hm f hf.1.
have [z hz] := @integrable_function_part_difference_defined R X mu hm f a%:E P N hf hp hn hP hN.
have hi := @measure_integral_from_parts R X mu hm f P N z hp hn hz.
have he := measure_integral_unique hi hf.
rewrite he in hz; have [hpfin hnfin] := nonnegative_difference_finite_sides hP hN hz.
have hPf : P < +oo by rewrite hpfin ltry.
have hNf : N < +oo by rewrite hnfin ltNyr.
have hsumfin : P+N \is a fin_num.
  rewrite ge0_fin_numE; first exact: lte_add_pinfty hPf hNf.
  exact: adde_ge0 hP hN.
exists (fine (P+N)); rewrite fineK //.
exact (@measure_absolute_integral_parts_sum R X mu hm f P N hp hn hP hN).
Qed.
