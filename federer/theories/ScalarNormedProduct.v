(** Federer (1969), 2.4.16, pp. 89–90: real products used to form admissible
    tests. The common-domain arithmetic is explicitly covered by 2.3.2, p.
    74. This adapter keeps values in the scalar norm metric; the existing
    extended product is finite everywhere on its domain, so projection
    changes no value. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  ExtendedFiniteProjectionBorel NormPowerScalar PartialFunctionUP PartialFunctionPair
  PartialFunctionPostcomposition PartialScalarProduct MeasureUP MeasurableFunctionUP
  MeasurablePostcomposition MeasurableGraphEquivalence BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_scalar_normed_product]: the real common-
    domain product used for tests in Federer 2.4.16, pp. 89–90,
    supporting arithmetic from 2.3.2, p. 74. *)
Definition partial_scalar_normed_product (R : realType) (X : Type)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  partial_function_postcompose (partial_function_pair f g)
    (fun p => (p.1 * p.2 : real_norm_metric_space (scalar_absolute_value_norm R))).

(** Source for [measurable_scalar_normed_product]: measurability
    of the real products used in Federer 2.4.16, pp. 89–90;
    an adapter for the already proved measurable arithmetic. *)
Lemma measurable_scalar_normed_product (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu g ->
  is_measure_measurable_function mu (partial_scalar_normed_product f g).
Proof.
move=> hf hg; have hp := @measurable_scalar_product R X mu hm f g hf hg.
have hreal := @measurable_function_borel_postcomposition R X (extended_real_line R)
  [the topologicalType of real_line_metric R] mu hm _
  (fun y => (fine y : real_line_metric R)) hp (@extended_finite_projection_borel R).
have hout := @measurable_function_borel_postcomposition R X [the topologicalType of real_line_metric R]
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm _
  (fun y => (y : real_norm_metric_space (scalar_absolute_value_norm R))) hreal
  (continuous_borel_function (@real_scalar_norm_identity_continuous R)).
apply: (@measurable_function_graph_equivalent R X _ mu _ _ _ hout)=> x z; split.
- move=> [r [[s [hs hsr]] hrz]].
  have [a [b [ha [hb hab]]]] := (partial_scalar_product_graph f g x s).1 hs.
  exists (a,b); split; first by split.
  by rewrite -hrz -hsr -hab.
- move=> [[a b] [[ha hb] hab]].
  exists (a*b); split=> //; exists (a*b)%:E; split=> //.
  apply/partial_scalar_product_graph; exists a,b; by split=> //; split.
Qed.

(** Source for [scalar_normed_same_domain_product_graph]: supporting
    graph identity for the powered-norm times sign test in Federer
    2.4.16, pp. 89–90. Both factors use the same original partial function. *)
Lemma scalar_normed_same_domain_product_graph (R : realType) (X Y : Type)
    (f : partial_function X Y) (P Q : Y -> real_norm_metric_space (scalar_absolute_value_norm R)) x z :
  partial_function_graph (partial_scalar_normed_product
    (partial_function_postcompose f P) (partial_function_postcompose f Q)) x z <->
  partial_function_graph (partial_function_postcompose f (fun y => P y * Q y)) x z.
Proof.
split.
- move=> [[a b] [[[v [hv hva]] [w [hw hwb]]] hab]].
  have hwv : w = v := partial_function_single_valued hw hv.
  rewrite hwv in hwb.
  exists v; split=> //; by rewrite hva hwb.
- move=> [v [hv he]]; exists (P v,Q v); split=> //; split; by exists v; split.
Qed.
