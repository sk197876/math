(** Federer (1969), 2.9.22, pp. 167–168: extend the finite family condition
    2.9.20(3), p. 165, to normed curves. This metric specification uses
    endpoint distances, strict individual cells and the printed non-strict
    bounds on both sums. No relevant erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import OrderedIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_interval_family_increment_sum]: supporting
    metric form of the increment sum in Federer 2.9.22,
    pp. 167–168, extending 2.9.20(3), p. 165. Sum the
    endpoint distances over the supplied finite interval family;
    the empty family has cost zero. *)
Definition metric_interval_family_increment_sum (R : realType) (Y : metricType R)
    (g : R -> Y) (s : seq (R * R)) : R :=
  \sum_(uv <- s) mdist (g uv.1) (g uv.2).

(** Source for [is_absolutely_continuous_metric_curve]: direct
    metric version of condition (3) in the extension asserted by
    Federer 2.9.22, pp. 167–168, of 2.9.20, p. 165.
    This abstract law presumes neither a derivative nor its integral.
    It retains strict individual interval lengths and both printed
    non-strict sum bounds; it applies in particular to norm metrics. *)
Definition is_absolutely_continuous_metric_curve (R : realType) (Y : metricType R)
    (g : R -> Y) (a b : R) := forall epsilon : R, 0<epsilon -> exists delta : R,
  0<delta /\ forall s : seq (R * R), is_ordered_real_interval_family a b s ->
    real_interval_family_length s<=delta -> metric_interval_family_increment_sum g s<=epsilon.
