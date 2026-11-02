(** Federer (1969), 2.3.8, pp. 78–79: closure under addition and scalar
    multiplication of the set A(mu,Y). Erratum p. 1, book p. 78 line 7,
    corrects the vector-space assertion for partial functions. Source
    editions: MeasurableNormedFunctionUP.v. All range witnesses are supplied
    by abstract closed-span laws. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric NormMetricContinuity
  NormMetricScaleContinuity MetricSubsetBackground PartialFunctionUP PartialFunctionPair
  PartialFunctionPostcomposition PartialNormedArithmetic MeasureUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurablePostcomposition BorelFunctionBasic
  MeasurableNormedFunctionUP EssentialSeparableEnvelope MeasurableSeparableRangeOperation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_normed_binary_operation]: supporting binary
    closure principle for Federer 2.3.8, p. 78 A continuous operation
    preserving each linear subspace preserves essential separability and
    measurability, even for a nonseparable ambient target. *)
Theorem measurable_normed_binary_operation (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN))
    (b : real_norm_metric_space hN * real_norm_metric_space hN -> real_norm_metric_space hN) :
  continuous b -> (forall (Z : subspace V) a z, Z a -> Z z -> Z (b (a,z))) ->
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  is_measurable_normed_function mu (partial_function_postcompose (partial_function_pair f g) b).
Proof.
move=> hb hstable [hf hsf] [hg hsg].
have [Z [hZ [[D [hc hd]] [hfs hgs]]]] :=
  @essential_separable_pair_envelope R X V N hN mu hm f g hsf hsg.
pose S : set (real_norm_metric_space hN) := fun y => Z y.
pose z0 : metric_subset S := @exist (real_norm_metric_space hN)
  (fun y => y \in S) 0%R (mem_set (subspace_zero Z)).
split.
- exact (@measurable_closed_separable_range_operation R X
    [the metricType R of real_norm_metric_space hN]
    [the topologicalType of real_norm_metric_space hN] mu hm S z0 D f g b
    hZ hc hd hb hf hg hfs hgs).
- exists Z; split; first by exists D.
  have hbad := @measure_null_union R X mu hm _ _ hfs hgs.
  apply: (@measure_null_subset R X mu hm _ _ _ hbad).
  move=> x [w [[[a z] [[ha hz] he]] hn]].
  have [hza|hza] := pselect (Z a); last by left; exists a; split.
  have [hzz|hzz] := pselect (Z z); last by right; exists z; split.
  exfalso; apply: hn; rewrite -he; exact: hstable hza hzz.
Qed.

(** Source for [measurable_normed_function_add]: direct additive closure of
    A(mu,Y) in Federer 2.3.8, p. 78 The sum retains exactly the common
    partial domain. *)
Theorem measurable_normed_function_add (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space hN)) :
  is_measurable_normed_function mu f -> is_measurable_normed_function mu g ->
  is_measurable_normed_function mu (partial_vector_add f g).
Proof.
move=> hf hg; apply: (@measurable_normed_binary_operation R X V N hN mu hm f g
  (fun p => (p.1+p.2)%R) _ _ hf hg).
- exact: real_norm_metric_add_continuous.
- move=> Z a z ha hz; exact: subspace_add ha hz.
Qed.

(** Source for [measurable_normed_function_scale]: scalar closure
    of A(mu,Y) used in Federer 2.3.8, p. 79.
    Multiplication by zero keeps the original conull domain;
    this does not identify all partial zero functions pointwise. *)
Theorem measurable_normed_function_scale (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R)
    (f : partial_function X (real_norm_metric_space hN)) :
  is_measurable_normed_function mu f ->
  is_measurable_normed_function mu (partial_vector_scale c f).
Proof.
move=> [hf [Z [hD hz]]]; split.
- apply: (@measurable_function_borel_postcomposition R X
    [the topologicalType of real_norm_metric_space hN]
    [the topologicalType of real_norm_metric_space hN] mu hm f (fun y => c *: y) hf).
  apply: continuous_borel_function; exact: real_norm_metric_scale_continuous.
- exists Z; split=> //.
  apply: (@measure_null_subset R X mu hm _ _ _ hz).
  move=> x [y [hy hn]]; have [a [ha he]] := proj1 (partial_vector_scale_graph c f x y) hy.
  exists a; split=> // hza; apply: hn; rewrite he; exact: subspace_scale hza.
Qed.
