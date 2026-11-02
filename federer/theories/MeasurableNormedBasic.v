(** Federer (1969), 2.3.8, pp. 78–79: constants and almost equality in
    A(mu,Y). The total-domain subcollection used for literal vector-space
    and convex-hull statements agrees; the whole collection retains
    Federer's partial domains and the erratum p. 1, book p. 78 line 7.
    Source context: MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages PartialFunctionExtensionUP MeasureUP MeasureBasic MeasureAlmostUP
  MeasureNullModification MeasurableFunctionUP MeasurableAlmostModification MeasurableTotalBasic
  MeasurableTotalExtension MetricSubsetBackground ClosedLinearSpanUP ClosedLinearSpanSealed
  MeasurableNormedFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_total_constant]: constants are
    members of A(mu,Y), supporting the function-space operations
    of Federer 2.3.8, pp. 78–79. A one-generator closed
    linear span supplies the essential-separability witness. *)
Lemma measurable_normed_total_constant (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (y : real_norm_metric_space hN) :
  is_measurable_normed_function mu (partial_function_total (fun _ : X => y)).
Proof.
split; first exact (@measurable_total_constant R X
  [the topologicalType of real_norm_metric_space hN] mu hm y).
pose D : set (real_norm_metric_space hN) := [set y].
pose Z := @ClosedLinearSpan.value R V N hN D.
have hZ := @ClosedLinearSpan.laws R V N hN D.
exists Z; split.
- exact: ClosedLinearSpan.countable_separable (countable1 y).
- rewrite partial_function_total_preimage.
  have he : (fun _ : X => y) @^-1` [set z | ~ Z z] = set0.
    apply/seteqP; split; last by move=> x [].
    move=> x hn; apply: hn; apply: (closed_linear_span_contains hZ); by [].
  rewrite he; exact: measure_empty.
Qed.

(** Source for [measurable_normed_almost_equal]: supporting
    invariance of A(mu,Y) under almost equality for Federer
    2.3.8, p. 78, consistent with 2.3.2, p. 73.
    The same separable subspace witnesses the new function. *)
Lemma measurable_normed_almost_equal (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measurable_normed_function mu f -> measure_almost_equal mu f g ->
  is_measurable_normed_function mu g.
Proof.
move=> [hf [Z [hD hz]]] he; split.
- exact (@measurable_function_almost_equal R X
    [the topologicalType of real_norm_metric_space hN] mu hm f g hf he).
- exists Z; split=> //.
  rewrite -(@almost_equal_preimage_measure R X (real_norm_metric_space hN)
    mu hm f g [set y | ~ Z y] he); exact hz.
Qed.

(** Source for [measurable_normed_total_representative]: supporting
    passage to total representatives in Federer 2.3.8, p. 78,
    using the extension assertion of 2.3.2, p. 73. This
    does not redefine A(mu,Y) to exclude partial functions. *)
Lemma measurable_normed_total_representative (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measurable_normed_function mu f -> exists g : X -> real_norm_metric_space hN,
    is_partial_function_total_extension f g /\ measure_almost_equal mu f (partial_function_total g) /\
    is_measurable_normed_function mu (partial_function_total g).
Proof.
move=> hf; have [g [he [ha hg]]] := @measurable_function_total_extension R X
  [the topologicalType of real_norm_metric_space hN] mu hm f 0%R hf.1.
exists g; split=> //; split=> //.
exact (@measurable_normed_almost_equal R X V N hN mu hm f _ hf ha).
Qed.
