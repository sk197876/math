(** Federer (1969), 3.1.4, p. 214: the Euclidean norm and its
    inner-product presentation give the same approximate limits. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm RealNormUP HilbertFormCompactness
  NormMetric InnerMetric FiniteNormEquivalence PartialFunctionUP MeasureApproximateLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [inner_norm_approximate_limit_iff]: supporting topology
    identification in the scalar reduction of Federer 3.1.4, p. 214.
    Only equality of neighborhood systems is used; the graph is unchanged. *)
Lemma inner_norm_approximate_limit_iff (R : realType) (X : metricType R)
    (Y : lmodType R) (B : Y -> Y -> R) (hB : is_inner_product B)
    (mu : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X Y) x y :
  @is_measure_approximate_limit R X
    [the topologicalType of real_norm_metric_space (inner_norm_real_norm hB)] mu V f x y <->
  @is_measure_approximate_limit R X
    [the topologicalType of inner_metric_space hB] mu V f x y.
Proof.
split=> hf U hU; apply: (@hf U).
- exact: (inner_real_norm_same_nbhs hB y U).1 hU.
- exact: (inner_real_norm_same_nbhs hB y U).2 hU.
Qed.
