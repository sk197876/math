(** Federer (1969), 3.1.4, p. 214: the two measurability
    conclusions for every finite-dimensional Euclidean target. This
    public combination includes the separate zero-target domain test. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  HilbertFormCompactness EuclideanLebesgueDimensions PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction ApproximatePartialDerivative MeasureUP MeasureRestriction
  MeasurableFunctionUP ApproximatePartialPositiveTargetMeasurable ApproximatePartialZeroTargetMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_approximate_partial_domain_measurable]:
    the first conclusion of Federer 3.1.4, p. 214, in all
    finite target dimensions and with the original conull source domain. *)
Theorem euclidean_approximate_partial_domain_measurable (R : realType) m n
    (A : set (R_n R m)) (f : R_n R m -> R_n R n) (i : 'I_m) :
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (@euclidean_lebesgue_measure R m) (partial_function_source_restrict A (partial_function_total f)) ->
  measure_measurable (@euclidean_lebesgue_measure R m) (partial_function_domain
    (approximate_partial_derivative (inner_norm_real_norm (@euclidean_inner_productP R n)) A f i)).
Proof.
case: n f=> [f hf|n f hf].
- exact: approximate_partial_zero_target_domain_measurable i hf.
- exact: approximate_partial_positive_target_domain_measurable i hf.
Qed.

(** Source for [euclidean_approximate_partial_measurable]: the
    second conclusion of Federer 3.1.4, p. 214. The measure
    is restricted to the exact sealed derivative domain, as printed. *)
Theorem euclidean_approximate_partial_measurable (R : realType) m n
    (A : set (R_n R m)) (f : R_n R m -> R_n R n) (i : 'I_m) :
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (@euclidean_lebesgue_measure R m) (partial_function_source_restrict A (partial_function_total f)) ->
  @is_measure_measurable_function R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R m)]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    (measure_restrict (@euclidean_lebesgue_measure R m) (partial_function_domain
      (approximate_partial_derivative (inner_norm_real_norm (@euclidean_inner_productP R n)) A f i)))
    (approximate_partial_derivative (inner_norm_real_norm (@euclidean_inner_productP R n)) A f i).
Proof.
case: n f=> [f hf|n f hf].
- exact: (@approximate_partial_zero_target_measurable R m A f i).
- exact: approximate_partial_positive_target_measurable i hf.
Qed.
