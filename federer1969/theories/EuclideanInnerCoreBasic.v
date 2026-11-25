(** Federer (1969), 3.2.42, printed p. 278:
    the actual radius-r inner core is closed and contained
    in the original source when r is positive. These facts
    supply measurability and finite volume before cancellation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  MetricOpenThickening TopologicalBorel MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_inner_core_subset]: supporting actual
    T subset S in the second proof paragraph of Federer
    3.2.42, p. 278. A point of the complement has distance
    zero from that complement, so cannot lie in a positive core. *)
Lemma positive_inner_core_subset (R:realType) (X:metricType R)
    (S:set X) (r:R):
  0<r ->(~`metric_open_thickening (~`S) r) `<=` S.
Proof.
move=>hr x hx; apply:contrapT=>hOutside; apply:hx.
exists x=>//; change (is_true (mdist x x<r)); by rewrite mdistxx.
Qed.

(** Source for [euclidean_inner_core_closed_measurable]: supporting
    closedness and actual Lebesgue measurability of T in
    Federer 3.2.42, p. 278. The original S may be arbitrary,
    and the core may be empty. *)
Lemma euclidean_inner_core_closed_measurable (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  closed (~`metric_open_thickening (~`S) r) /\
  measure_measurable (@euclidean_lebesgue_measure R n)
    (~`metric_open_thickening (~`S) r).
Proof.
have hClosed:closed (~`metric_open_thickening (~`S) r):=
  open_closedC (metric_open_thickening_open (~`S) r).
split; first exact hClosed.
apply:euclidean_borel_measurable; exact:closed_borel_set hClosed.
Qed.
