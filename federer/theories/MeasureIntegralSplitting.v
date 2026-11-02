(** Federer (1969), 2.4.10, p. 85: splitting over a measurable set,
    underlying the interval-additivity assertion at the end of the item.
    Both directions of definedness are retained through the partial extended
    sum. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  PartialZeroExtensionSplit MeasureUP MeasureFiniteClosure MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralPartsExist MeasureIntegralPartsDifference MeasureIntegralRestriction
  MeasureIntegralAddition MeasureIntegralGraphEquivalence NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_integral_measurable_split]: Supporting Federer
    2.4.10, p. 85.This equivalence states when each side of the signed
    formula exists, rather than assigning values to opposite infinities. *)
Theorem measure_integral_measurable_split (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) a :
  measure_measurable mu A ->
  (is_measure_integral mu f a <-> exists b c,
    is_measure_integral mu (partial_function_zero_extension (0 : extended_real_line R) A f) b /\
    is_measure_integral mu (partial_function_zero_extension (0 : extended_real_line R) (~` A) f) c /\
    extended_add b c=Some a).
Proof.
move=> hA; split.
- move=> hf; have [P [N [hP [hN [hP0 hN0]]]]] := @measurable_function_parts_integrals R X mu hm f hf.1.
  have [z hz] := @integrable_function_part_difference_defined R X mu hm f a P N hf hP hN hP0 hN0.
  have [b [hb [hbp hbn]]] := @measure_restricted_integral_finite_sides R X mu hm A f P N z hA hf.1 hP hN hP0 hN0 hz.
  have [c [hc [hcp hcn]]] := @measure_restricted_integral_finite_sides R X mu hm (~` A) f P N z
    (measure_measurable_complement hA) hf.1 hP hN hP0 hN0 hz.
  have hside : (P < +oo) || (N < +oo).
    apply: (proj1 (nonnegative_difference_defined hP0 hN0)); by exists z.
  have hadd : adde_def b c.
    move/orP: hside=> [hpos|hneg].
    + exact: ltpinfty_adde_def (hbp hpos) (hcp hpos).
    + exact: ltninfty_adde_def (hbn hneg) (hcn hneg).
  have hs : extended_add b c=Some (b+c) by rewrite /extended_add hadd.
  have hi := @measure_integral_add R X mu hm _ _ b c (b+c) hb hc hs.
  have hi' := @measure_integral_graph_equivalent R X mu _ f (b+c) (partial_zero_extension_split_graph A f) hi.
  have he := measure_integral_unique hi' hf.
  exists b,c; split=> //; split=> //; by rewrite -he.
- move=> [b [c [hb [hc hs]]]].
  have hi := @measure_integral_add R X mu hm _ _ b c a hb hc hs.
  exact: measure_integral_graph_equivalent (partial_zero_extension_split_graph A f) hi.
Qed.
