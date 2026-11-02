(** Federer (1969), 2.2.15, p. 71, final target criterion: abstract curves
    approximating successive finite prefixes of a sequence of target values.
    This supports the sufficiency argument, which is not printed in the
    book. *)
From mathcomp Require Import all_boot all_algebra reals topology.
From Federer Require Import RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_curve_sequence_approximation]: supporting
    curve and parameter laws for Federer 2.2.15, p. 71.
    Curve n approximates the first n+1 target values within
    1/(n+1); parameters outside that prefix are unrestricted. *)
Record is_curve_sequence_approximation (R : realType) (Y : metricType R)
    (y : nat -> Y) (c : nat -> real_line_metric R -> Y) (t : nat -> nat -> R) : Prop := {
  curve_sequence_continuous : forall n, continuous (c n);
  curve_sequence_error : forall n i, (i <= n)%N ->
    mdist (y i) (c n (t n i)) < ((n.+1)%:R)^-1
}.
