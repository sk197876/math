(** Federer (1969), 3.1.4, p. 214: the scalar approximate partial
    derivative has measurable domain and is measurable for the measure
    restricted to that domain. The exact sealed derivative is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions RealMetricBackground RealNormUP NormMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages PartialFunctionSourceRestriction
  PartialFunctionPostcomposition CoordinateDifferenceQuotient CoordinateDifferenceQuotientMeasurable
  ApproximatePartialDerivative ApproximatePartialOrderValues ScalarApproximateTargetTopology
  EuclideanApproximateOrderMeasurable MeasurableFiniteExtendedAgreement
  MeasureUP MeasureBasic MeasureFiniteClosure MeasureRestriction MeasureAlmostUP
  MeasurableFunctionUP MeasurableFunctionBorel MeasurablePostcomposition
  MeasurableGraphEquivalence MeasurableRealEmbedding MeasurableRealPairs MeasurableOrderRays
  BorelFunctionBasic CountableOrderIntervals ExtendedRealOrderTopology ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ScalarMeasurability.
Variable R : realType.
Variable n : nat.
Variable i : 'I_n.
Variable A : set (R_n R n).
Variable f : R_n R n -> R^o.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation F := (partial_function_source_restrict A
  (partial_function_total (fun x=>(f x : real_line_metric R)))).
Hypothesis hf : is_measure_measurable_function Leb F.

(** Source for [approximate_partial_scalar_order_values_measurable]:
    the measurability of g_i and its lower-limit companion asserted
    in the first proof paragraph of Federer 3.1.4, p. 214. *)
Theorem approximate_partial_scalar_order_values_measurable :
  @is_measure_measurable_function R [the choiceType of E] [the topologicalType of extended_real_line R]
    Leb (partial_function_total (@approximate_partial_upper_value R n i A f)) /\
  @is_measure_measurable_function R [the choiceType of E] [the topologicalType of extended_real_line R]
    Leb (partial_function_total (@approximate_partial_lower_value R n i A f)).
Proof.
have hq := euclidean_joint_coordinate_quotient_measurable i hf.
have hqe := @measurable_function_borel_postcomposition R _
  [the topologicalType of real_line_metric R] [the topologicalType of extended_real_line R] _
  (product_measure_is_measure hm (euclidean_lebesgue_is_measure R 1)) _
  (fun y : real_line_metric R=>(y%:E : extended_real_line R)) hq
  (continuous_borel_function (@real_extended_embedding_continuous R)).
split; [exact: euclidean_approximate_upper_limit_measurable hqe|
  exact: euclidean_approximate_lower_limit_measurable hqe].
Qed.

(** Source for [approximate_partial_scalar_domain_measurable]: the
    first conclusion of Federer 3.1.4, p. 214, for a scalar target.
    The original conull base domain is explicitly intersected with the
    finite equality locus of the two approximate order limits. *)
Theorem approximate_partial_scalar_domain_measurable :
  measure_measurable Leb (partial_function_domain
    (approximate_partial_derivative (scalar_absolute_value_norm R) A f i)).
Proof.
have hA := @conull_partial_function_domain_measurable R [the choiceType of E]
  (real_line_metric R) Leb hm F (measurable_function_domain hf).
rewrite partial_function_source_restrict_domain partial_function_total_domain setIT in hA.
rewrite approximate_partial_scalar_order_domain.
apply: (@measure_measurable_intersection R [the choiceType of E] Leb hm A _ hA).
have [hu hl] := approximate_partial_scalar_order_values_measurable.
exact: (@measurable_finite_extended_agreement R [the choiceType of E] Leb hm
  (@approximate_partial_upper_value R n i A f) (@approximate_partial_lower_value R n i A f) hu hl).
Qed.

(** Source for [approximate_partial_scalar_measurable]: the second
    conclusion of Federer 3.1.4, p. 214, for a scalar target. Rational
    rays of the derivative are its domain intersected with rays of g_i.
    Measurability is with respect to the restricted measure, as printed. *)
Theorem approximate_partial_scalar_measurable :
  @is_measure_measurable_function R [the choiceType of E]
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
    (measure_restrict Leb (partial_function_domain
      (approximate_partial_derivative (scalar_absolute_value_norm R) A f i)))
    (approximate_partial_derivative (scalar_absolute_value_norm R) A f i).
Proof.
pose D := approximate_partial_derivative (scalar_absolute_value_norm R) A f i.
pose Ai := partial_function_domain D.
pose mu := measure_restrict Leb Ai.
pose hmu := measure_restrict_is_measure hm Ai.
have hAi := approximate_partial_scalar_domain_measurable.
have [hu hl] := approximate_partial_scalar_order_values_measurable.
have hd : measure_almost_everywhere mu (partial_function_domain D).
  change (Leb (Ai `&` (~` Ai))=0%E).
  rewrite setICr; exact: measure_empty hm.
have hDr : @is_measure_measurable_function R [the choiceType of E]
    [the topologicalType of real_line_metric R] mu D.
  apply: (@measurable_order_dense_rays_iff R [the choiceType of E] _
    [the orderTopologicalType _ of R^o] [the countType of (rat : Type)]
    mu hmu D (fun q=>ratr q) (@real_rationals_order_dense R) hd).2=> q.
  have he : partial_function_preimage D [set y | y<(ratr q : R)]=
      Ai `&` partial_function_preimage
        (partial_function_total (@approximate_partial_upper_value R n i A f))
        [set y : extended_real_line R | (y<(ratr q : R)%:E)%E].
    apply/seteqP; split=> a.
    - move=> [c [hc hcq]]; split; first by exists c.
      have [_ [huc _]] := (approximate_partial_scalar_order_graph i A f a c).1 hc.
      exists c%:E; split=> //; by rewrite /= lte_fin.
    - move=> [[c hc] [v [hv hvq]]].
      have [_ [huc _]] := (approximate_partial_scalar_order_graph i A f a c).1 hc.
      exists c; split=> //.
      change (approximate_partial_upper_value i A f a=v) in hv.
      by move: hvq; rewrite /= -hv huc lte_fin.
  rewrite he; apply: measure_restrict_measurable.
  apply: (@measure_measurable_intersection R [the choiceType of E] Leb hm Ai _ hAi).
  exact: (measurable_function_open_preimage hu
    (@order_strict_lower_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] (ratr q : R)%:E)).
have hDn := @measurable_function_borel_postcomposition R [the choiceType of E]
  [the topologicalType of real_line_metric R]
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hmu D
  (fun z=>(z : real_norm_metric_space (scalar_absolute_value_norm R))) hDr
  (continuous_borel_function (@real_scalar_norm_identity_continuous R)).
apply: (@measurable_function_graph_equivalent R [the choiceType of E]
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)]
  mu _ D _ hDn)=> a c.
split; first by move=> [v [hv <-]].
by move=> hc; exists c.
Qed.
End ScalarMeasurability.
