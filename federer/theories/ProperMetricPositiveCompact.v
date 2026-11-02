(** Federer (1969), 3.2.18, p. 255:
    compact inner selection from a finite
    measurable positive-mass subset, using 2.2.3.
    The ambient Hausdorff measure need not
    be locally finite or globally Radon. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit
  BorelRegularMeasureUP LipschitzFunctionCompact ProperMetricCompactApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [proper_metric_positive_compact_subset]:
    the compact inner-approximation step of
    Federer 3.2.18, p. 255, citing
    2.2.3. Only the selected measurable
    set is required to have finite measure. *)
Theorem proper_metric_positive_compact_subset (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (A : set X) (a : X) :
  is_measure mu -> is_borel_regular_measure mu -> metric_boundedly_compact X ->
  measure_measurable mu A -> mu A< +oo -> 0<mu A ->
  exists C, compact C /\ C `<=` A /\ 0<mu C.
Proof.
move=> hm hReg hX hA hFin hPos.
have [K [hK [hKA [_ hNull]]]] := @proper_metric_finite_compact_approximation R X mu hm hReg A a hX hA hFin.
case: (pselect (exists n, 0<mu (K n)))=> [[n hn]|hNone].
- exists (K n); split; first exact: hK n.
  split; [exact: hKA n|exact hn].
- have hZero n : mu (K n)=0.
    apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
    apply/negP=> hp; apply: hNone; by exists n.
  have hUnion := @measure_null_countable_union R X nat mu hm setT K (countableP _) (fun n _=>hZero n).
  have hCover : A `<=` (A `\` (\bigcup_n K n)) `|` (\bigcup_n K n).
    move=> x hx; case: (pselect ((\bigcup_n K n) x))=> hh; [by right|by left; split].
  have hb := measure_binary_cover hm hCover.
  rewrite hNull hUnion add0e in hb.
  by have := lt_le_trans hPos hb; rewrite ltxx.
Qed.
