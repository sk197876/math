(** Federer (1969), 3.1.4, p. 214: the zero-dimensional target
    boundary. Coordinate conditions alone would be empty, so the scalar
    zero quotient retains the necessary coordinate-line domain density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  HilbertFormCompactness InnerMetric RealNormUP NormMetric RealMetricBackground
  EuclideanLebesgueDimensions PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialFunctionPostcomposition MeasureApproximateLimitUP
  ApproximatePartialDerivativeUP ApproximatePartialDerivative ConstantPartialApproximateLimit
  ScalarApproximatePartialMeasurable MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP
  MeasurableFunctionUP MeasurablePostcomposition BorelFunctionBasic MeasurableGraphEquivalence
  MeasurableEuclideanCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ZeroTarget.
Variable R : realType.
Variable m : nat.
Variable A : set (R_n R m).
Variable f : R_n R m -> R_n R 0.
Variable i : 'I_m.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R 0)).
Local Notation Leb := (@euclidean_lebesgue_measure R m).
Local Notation hm := (euclidean_lebesgue_is_measure R m).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R 0)).
Local Notation hS := (scalar_absolute_value_norm R).
Local Notation D := (approximate_partial_derivative hN A f i).
Local Notation Dz := (approximate_partial_derivative hS A (fun _=>0) i).

(** Source for [approximate_partial_zero_target_scalar_criterion]:
    the empty-target boundary of the scalar reduction in Federer
    3.1.4, p. 214. Both zero quotients have the same punctured
    actual domain; their limits require density zero of its complement. *)
Lemma approximate_partial_zero_target_scalar_criterion a :
  has_approximate_partial_derivative hN A f a i 0 <->
  has_approximate_partial_derivative hS A (fun _=>0) a i 0.
Proof.
have hz t z : partial_function_graph (approximate_partial_quotient hN A f a i) t z -> z=0.
  move=> _; apply/ffunP=> j; by have := ltn_ord j; rewrite ltn0.
have hs t z : partial_function_graph (approximate_partial_quotient hS A (fun _=>0) a i) t z -> z=0.
  by move=> [_ <-]; rewrite subrr scaler0.
rewrite /has_approximate_partial_derivative
  (constant_partial_approximate_limit_iff _ _ _ hz)
  (constant_partial_approximate_limit_iff _ _ _ hs)
  /approximate_partial_quotient !partial_function_source_restrict_domain
  !partial_function_total_domain !setIT.
by [].
Qed.

(** Source for [approximate_partial_zero_target_domain]: the
    first conclusion of Federer 3.1.4, p. 214, at zero target
    dimension, with the domain encoded by the scalar zero function. *)
Lemma approximate_partial_zero_target_domain :
  partial_function_domain D=partial_function_domain Dz.
Proof.
apply/seteqP; split=> a [v hv].
- have hv0 : v=0 by apply/ffunP=> j; have := ltn_ord j; rewrite ltn0.
  exists 0; apply: (approximate_partial_derivative_graph hS A _ i a 0).2.
  apply: (approximate_partial_zero_target_scalar_criterion a).1.
  move: hv; rewrite hv0 approximate_partial_derivative_graph; by [].
- have [ha hl] := (approximate_partial_derivative_graph hS A _ i a v).1 hv.
  have hd := approximate_limit_domain_density hl.
  exists 0; apply: (approximate_partial_derivative_graph hN A f i a 0).2.
  apply: (approximate_partial_zero_target_scalar_criterion a).2; split=> //.
  apply: (constant_partial_approximate_limit_iff _ _ _ _).2 hd.
  by move=> t z [_ <-]; rewrite subrr scaler0.
Qed.

Hypothesis hf : @is_measure_measurable_function R [the choiceType of X]
  [the topologicalType of Y] Leb (partial_function_source_restrict A (partial_function_total f)).

(** Source for [approximate_partial_zero_target_domain_measurable]:
    measurable derivative domain in Federer 3.1.4, p. 214,
    including zero target dimension without a vacuous coordinate test. *)
Theorem approximate_partial_zero_target_domain_measurable :
  measure_measurable Leb (partial_function_domain D).
Proof.
rewrite approximate_partial_zero_target_domain.
have hc : continuous (fun _ : Y=>(0 : real_line_metric R)).
  exact: cst_continuous.
have hh := measurable_function_borel_postcomposition hm hf (continuous_borel_function hc).
have hz : @is_measure_measurable_function R [the choiceType of X]
    [the topologicalType of real_line_metric R] Leb
    (partial_function_source_restrict A (partial_function_total (fun _=>0))).
  apply: (measurable_function_graph_equivalent _ hh)=> x c.
  split; first by move=> [v [[ha _] <-]].
  by move=> [ha <-]; exists (f x); split=> //; split.
exact: approximate_partial_scalar_domain_measurable hz.
Qed.

(** Source for [approximate_partial_zero_target_measurable]:
    measurable approximate partial derivative in Federer 3.1.4,
    p. 214, with singleton target. Conullness for the restricted
    measure is proved separately from the empty coordinate family. *)
Theorem approximate_partial_zero_target_measurable :
  @is_measure_measurable_function R [the choiceType of X] [the topologicalType of Y]
    (measure_restrict Leb (partial_function_domain D)) D.
Proof.
pose Ai := partial_function_domain D.
have hd : measure_almost_everywhere (measure_restrict Leb Ai) Ai.
  change (Leb (Ai `&` (~` Ai))=0%E); rewrite setICr; exact: measure_empty hm.
apply: (measurable_euclidean_coordinate_criterion (measure_restrict_is_measure hm Ai) hd).2.
by move=> j; have := ltn_ord j; rewrite ltn0.
Qed.
End ZeroTarget.
