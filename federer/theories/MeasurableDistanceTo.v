(** Federer (1969), 2.9.9, pp. 156–157: fixed-target distance functions in
    the Lebesgue-point proof. We retain Federer's exponent one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionPostcomposition MetricPairDistance
  NormMetricScaleContinuity MeasurableRealEmbedding BorelFunctionBasic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurablePostcomposition PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [partial_distance_to]: direct scalar function mapping
    z to the distance from f(z) to y in Federer 2.9.9, proof p. 157.
    This supporting definition works in any metric target; in a normed
    space the distance is the norm of the difference. *)
Definition partial_distance_to (R : realType) (X : Type) (Y : metricType R)
    (f : partial_function X Y) (y : Y) : partial_function X (extended_real_line R) :=
  partial_function_postcompose f (fun z => ((mdist z y)%:E : extended_real_line R)).

(** Source for [metric_distance_to_continuous]: supporting continuity of the
    scalar distance function used in Federer 2.9.9, p. 157 This is proved
    from the triangle inequality, without a normed-space construction. *)
Lemma metric_distance_to_continuous (R : realType) (Y : metricType R) (y : Y) :
  continuous (fun z : Y => ((mdist z y)%:E : extended_real_line R)).
Proof.
have hc : continuous (fun z : Y => (mdist z y : real_line_metric R)).
  apply: (@metric_fixed_lipschitz_continuous R Y (real_line_metric R) _ 1)=> // a b.
  change (`|mdist a y-mdist b y| <= 1*mdist a b)%R.
  rewrite mul1r; have h := metric_pair_distance_change_bound a y b y.
  by rewrite mdistxx addr0 in h.
move=> z; exact (@continuous_comp Y (real_line_metric R) (extended_real_line R)
  (fun z => (mdist z y : real_line_metric R)) (fun r => r%:E) z
  (hc z) (@real_extended_embedding_continuous R (mdist z y))).
Qed.

(** Source for [measurable_partial_distance_to]: supporting application of
    scalar differentiation to each fixed y in Federer 2.9.9, p. 157 No
    separability is needed for this step. *)
Lemma measurable_partial_distance_to (R : realType) (X : choiceType) (Y : metricType R)
    (phi : set X -> \bar R) (f : partial_function X Y) y :
  is_measure phi -> is_measure_measurable_function phi f ->
  is_measure_measurable_function phi (partial_distance_to f y).
Proof.
move=> hm hf; apply: (@measurable_function_borel_postcomposition R X Y
  (extended_real_line R) phi hm f _ hf).
apply: continuous_borel_function; exact: metric_distance_to_continuous.
Qed.

(** Source for [partial_distance_to_nonnegative]: supporting
    nonnegativity in the scalar application of Federer 2.9.8 inside
    2.9.9, p. 157. The original partial domain is preserved. *)
Lemma partial_distance_to_nonnegative (R : realType) (X : choiceType) (Y : metricType R)
    (phi : set X -> \bar R) (f : partial_function X Y) y :
  is_measure phi -> is_measure_measurable_function phi f ->
  measure_almost_everywhere phi (partial_extended_nonnegative_locus (partial_distance_to f y)).
Proof.
move=> hm hf; apply: (@measure_almost_everywhere_mono R X phi hm _ _ _
  (measurable_function_domain hf))=> x [z hz].
exists (mdist z y)%:E; split; [by exists z; split|by rewrite lee_fin mdist_ge0].
Qed.
