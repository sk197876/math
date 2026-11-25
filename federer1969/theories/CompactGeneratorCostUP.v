(** Federer (1969), 2.10.22, p. 184: the cost on all nonempty compact
    subsets is finite, nonnegative, continuous for the Hausdorff metric, and
    strictly positive on sets of positive diameter. This predicate records
    exactly these hypotheses; it does not assume the continuity-below
    conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_continuous_positive_compact_cost]: direct
    cost hypotheses of 2.10.22, p. 184.
    Real-valued costs are finite; zero is permitted
    on zero-diameter compact sets. *)
Record is_continuous_positive_compact_cost (R : realType) (X : metricType R)
    (cost : compact_metric_set X -> R) : Prop := {
  (** Source for [compact_cost_nonnegative_law]: direct
      nonnegativity hypothesis in 2.10.22, p. 184. *)
  compact_cost_nonnegative_law : forall C, 0<=cost C;
  (** Source for [compact_cost_continuous_law]: direct
      Hausdorff-continuity hypothesis in 2.10.22, p. 184. *)
  compact_cost_continuous_law : continuous (fun C : compact_hausdorff_space X => (cost C : real_line_metric R));
  (** Source for [compact_cost_positive_diameter_law]: direct
      positivity on positive-diameter sets in 2.10.22,
      p. 184. Singleton costs need not be zero. *)
  compact_cost_positive_diameter_law : forall C, 0<compact_metric_diameter C -> 0<cost C
}.
