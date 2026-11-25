(** Supporting range reduction for Federer (1969), 2.3.6, p. 77, final
    paragraph: map into a nonempty closed separable support, preserving its
    points. Source context: ContinuousClosedPieceBorel.v. The retraction is
    Borel, and no continuous retraction onto an arbitrary closed set is
    asserted. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import MetricSubsetBackground BorelFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_closed_subset_borel_retraction]: supporting
    abstract range-reduction map for Federer 2.3.6, p. 77.
    Its values lie in S by their subtype, and it fixes every point of S. *)
Definition is_closed_subset_borel_retraction (R : realType) (Y : metricType R)
    (S : set Y) (r : Y -> metric_subset S) :=
  is_borel_function r /\ forall y, S y -> val (r y) = y.
