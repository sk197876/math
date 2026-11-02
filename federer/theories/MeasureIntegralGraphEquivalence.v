(** Federer (1969), proof of 2.4.4(3)–(6), p. 83: supporting substitution of
    pointwise numerical identities in integral assertions. Graph equivalence
    preserves exact partial domains, including undefined sums of infinities.
    Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureIntegralUP
  MeasurableGraphEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_step_loci_graph_equivalent]: supporting
    invariance of the upper and lower comparisons used in
    Federer 2.4.4, pp. 82–83. *)
Lemma partial_step_loci_graph_equivalent (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  forall u, partial_step_upper_locus u f = partial_step_upper_locus u g /\
    partial_step_lower_locus u f = partial_step_lower_locus u g.
Proof.
move=> he u; split; apply/seteqP; split=> x [y [z [hy [hz hle]]]];
  exists y,z; split=> //; split=> //.
- exact: (he x z).1 hz.
- exact: (he x z).2 hz.
- exact: (he x z).1 hz.
- exact: (he x z).2 hz.
Qed.

(** Source for [measure_step_value_families_graph_equivalent]:
    supporting invariance of the two approximant families under
    the numerical identities in Federer 2.4.4, p. 83. *)
Lemma measure_step_value_families_graph_equivalent (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : partial_function X (extended_real_line R)) :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  measure_upper_step_values mu f = measure_upper_step_values mu g /\
  measure_lower_step_values mu f = measure_lower_step_values mu g.
Proof.
move=> he; split; apply/seteqP; split=> a [u [[hu hlu] ha]];
  exists u; split=> //; split=> //.
- by rewrite -(partial_step_loci_graph_equivalent he u).1.
- by rewrite (partial_step_loci_graph_equivalent he u).1.
- by rewrite -(partial_step_loci_graph_equivalent he u).2.
- by rewrite (partial_step_loci_graph_equivalent he u).2.
Qed.

(** Source for [measure_integral_graph_equivalent]: supporting
    substitution principle for the identities used in Federer
    2.4.4(3)–(6), p. 83; no default values are assigned
    to points outside either graph. *)
Lemma measure_integral_graph_equivalent (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f g : partial_function X (extended_real_line R)) a :
  (forall x y, partial_function_graph f x y <-> partial_function_graph g x y) ->
  is_measure_integral mu f a -> is_measure_integral mu g a.
Proof.
move=> he [hf [hu hl]]; have [eu el] := measure_step_value_families_graph_equivalent mu he.
split.
- exact: measurable_function_graph_equivalent he hf.
- split.
  + by rewrite /is_measure_upper_integral -eu.
  + by rewrite /is_measure_lower_integral -el.
Qed.
