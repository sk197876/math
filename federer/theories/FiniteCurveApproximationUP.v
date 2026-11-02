(** Federer (1969), 2.2.15, p. 71, final paragraph: the finite-set
    approximation condition on the target metric space. We state the
    condition literally, including the empty finite set, and treat its
    empty-target boundary separately. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [has_finite_curve_approximation]: direct target
    condition in Federer 2.2.15, p. 71: every finite
    subset lies in the epsilon-neighborhood of the image of a
    continuous real-parameter curve, for every positive epsilon. *)
Definition has_finite_curve_approximation (R : realType) (Y : metricType R) : Prop :=
  forall Z : set Y, finite_set Z -> forall epsilon : R, 0 < epsilon ->
    exists c : real_line_metric R -> Y, continuous c /\
      forall z, Z z -> exists t, mdist z (c t) < epsilon.
