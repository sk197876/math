(** Federer (1969), 2.4.10, p. 85: measurability of fg with zero times
    infinity set to zero. The scalar product is Borel: it is continuous on
    the ordinary multiplication domain and identically zero on its
    complement. Source context: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPair PartialFunctionPostcomposition
  PartialDensityProduct MeasureUP MeasurableFunctionUP MeasurableExtendedPairs MeasurablePostcomposition
  MeasurableGraphEquivalence TopologicalBorel BorelFunctionUP BorelContinuousRegion ExtendedArithmeticDomains ExtendedArithmeticContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [density_product_outside_ordinary_domain]: the exceptional
    pairs in the density product of Federer 2.4.10, p. 85, have assigned
    value zero. *)
Lemma density_product_outside_ordinary_domain (R : realType) (a b : \bar R) :
  ~ mule_def a b -> a*b=0.
Proof.
move=> hn; have [he|he] := eqVneq (a*b) 0; first exact he.
exfalso; apply: hn; exact (@neq0_mule_def R a b he).
Qed.

(** Source for [extended_zero_product_borel]: supporting Borel
    measurability of the scalar product with the zero-infinity
    convention in Federer 2.4.10, p. 85. *)
Lemma extended_zero_product_borel (R : realType) :
  is_borel_function (fun p : extended_real_line R * extended_real_line R => (p.1 * p.2 : extended_real_line R)).
Proof.
pose D := [set p : extended_real_line R * extended_real_line R | mule_def p.1 p.2].
pose m := fun p : extended_real_line R * extended_real_line R => (p.1 * p.2 : extended_real_line R).
have hD : borel_set D := extended_multiply_domain_borel R.
have hc p : D p -> {for p, continuous m} := @extended_multiply_continuous_at_defined R p.
have hk := @borel_continuous_region_extension _ (extended_real_line R) D m 0 hD hc.
have he : (fun p => if pselect (D p) then m p else 0) = m.
  apply/funext=> p; case: p=> a b.
  case: (pselect (D (a,b)))=> // hn.
  symmetry; exact: density_product_outside_ordinary_domain hn.
by rewrite he in hk.
Qed.

(** Source for [measurable_density_product]: supporting measurable
    product in the change-of-density formula of Federer
    2.4.10, p. 85. Both input domains are
    conull; no exclusion of zero-infinity pairs is required. *)
Lemma measurable_density_product (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f h : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu h ->
  is_measure_measurable_function mu (partial_density_product f h).
Proof.
move=> hf hh.
have hp := @measurable_extended_function_pair R X mu hm f h hf hh.
have hv := @measurable_function_borel_postcomposition R X _ (extended_real_line R) mu hm
  (partial_function_pair f h) (fun p => (p.1 * p.2 : extended_real_line R)) hp (@extended_zero_product_borel R).
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hv)=> x z.
rewrite partial_density_product_graph; split.
- move=> [[a b] [[ha hb] he]]; exists a,b; by split=> //; split.
- move=> [a [b [ha [hb he]]]]; exists (a,b); by split; first split.
Qed.
