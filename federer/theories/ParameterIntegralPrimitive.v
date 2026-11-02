(** Federer (1969), 2.9.25, p. 169: Fubini writes g(t) as the prefix
    integral of y mapped to integral u(x,y) dphi x. This file derives that
    actual primitive relation, including summability of the partial inner
    integral. We represent u outside the closed interval by zero for proof
    purposes; no exterior value is assumed in the statement or used by the
    conclusion. No relevant local erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws PartialProductSections
  MeasureUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureSubsetIntegral
  ProductMeasure ProductSummableFubini ProductSubsetInterchange
  ParameterizedIntegral ParameterizedIntegralLaws LebesgueScalarMeasure
  BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [product_nested_subset_vertical_graph]: supporting
    restriction identity for the prefix intervals in Federer
    2.9.25, p. 169. Restricting a section first to I and
    then to B contained in I has exactly the graph of its
    restriction to B, including undefined original values. *)
Lemma product_nested_subset_vertical_graph (X Y Z : Type) (zero : Z)
    (I B : set Y) (f : partial_function (X*Y) Z) : B `<=` I -> forall x y z,
  partial_function_graph (partial_function_zero_extension zero B
    (partial_product_vertical_section (partial_function_zero_extension zero (setT `*` I) f) x)) y z <->
  partial_function_graph (partial_function_zero_extension zero B
    (partial_product_vertical_section f x)) y z.
Proof.
move=> hBI x y z; case: (pselect (B y))=> hy.
- rewrite !(partial_function_zero_extension_on _ _ _ hy).
  rewrite product_subset_vertical_graph.
  exact: partial_function_zero_extension_on (hBI y hy).
- by rewrite !(partial_function_zero_extension_off _ _ _ hy).
Qed.

(** Source for [parameter_integral_prefix_primitive]: direct Fubini
    representation in Federer 2.9.25, p. 169 The finite joint subset
    integral suffices for arbitrary phi; no ambient sigma-finiteness
    hypothesis is imposed. All inner and outer assertions retain actual
    integrability domains. *)
Theorem parameter_integral_prefix_primitive (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (hp : is_measure phi)
    (f : partial_function (X*real_line_metric R) (extended_real_line R))
    (g : R -> R) (a b J : R) :
  is_measure_subset_integral (product_measure hp (lebesgue_scalar_is_measure R))
    (setT `*` `[a,b]) f J%:E ->
  (forall t : R, a<=t -> t<=b -> is_measure_integral phi
    (parameterized_integral (@lebesgue_scalar_measure R) (fun x =>
      partial_function_zero_extension (0 : extended_real_line R) `[a,t]
        (partial_product_vertical_section f x))) (g t)%:E) ->
  let F := partial_function_zero_extension (0 : extended_real_line R) (setT `*` `[a,b]) f in
  let h := parameterized_integral phi (partial_product_horizontal_section F) in
  is_measure_summable (@lebesgue_scalar_measure R) h /\
  (forall t : R, a<=t -> t<=b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,t] h (g t)%:E).
Proof.
move=> hJ hG F h; pose hL := lebesgue_scalar_is_measure R.
have hsum : is_measure_summable (product_measure hp hL) F by exists J; exact hJ.
have [_ hH] := @product_summable_fubini R X (real_line_metric R) phi
  (@lebesgue_scalar_measure R) hp hL F J hJ.
split; first by exists J.
move=> t hat htb.
have hIt : measure_measurable (@lebesgue_scalar_measure R) `[a,t].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R a t).
have hsub : (`[a,t] : set (real_line_metric R)) `<=` `[a,b].
  move=> y; rewrite /= !in_itv /= => /andP[hay hyt].
  by rewrite hay (le_trans hyt htb).
apply: (@product_summable_subset_interchange R X (real_line_metric R) phi
  (@lebesgue_scalar_measure R) hp hL F `[a,t] (g t)%:E hsum hIt).
apply: (@measure_integral_graph_equivalent R X phi _ _ (g t)%:E _ (hG t hat htb)).
apply: parameterized_integral_graph_equivalent=> x y z.
symmetry; exact (@product_nested_subset_vertical_graph X (real_line_metric R)
  (extended_real_line R) 0 `[a,b] `[a,t] f hsub x y z).
Qed.
