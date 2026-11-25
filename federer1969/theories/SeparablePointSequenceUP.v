(** Federer (1969), 2.4.12, p. 87: supporting dense candidate sequence for
    finite-image approximation in a separable target. A distinguished first
    point allows zero to be included without altering density. *)
From mathcomp Require Import all_boot classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_based_dense_sequence]: abstract supporting laws
    for the separable approximation in Federer 2.4.12, p. 87.
    The first value is prescribed and the entire image is dense. *)
Definition is_based_dense_sequence (R : realType) (Y : metricType R)
    (y0 : Y) (y : nat -> Y) := y 0%N=y0 /\ dense (y @` setT).
