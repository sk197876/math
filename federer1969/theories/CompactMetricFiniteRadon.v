(** Federer (1969), 3.3.4, p. 290: the
    finite Borel regular reference on the actual
    compact projective carrier is Radon. This
    general supporting metric proof uses closed
    compact balls and the open-approximation laws
    of 2.2.2–2.2.3, pp. 61–62. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP
  TopologicalBorel RadonMeasureUP SubtypeCompactHausdorff MetricClosedBalls
  LipschitzFunctionCompact StructureOpenCompactInner FiniteBorelOpenInfimum
  ExtendedRealReciprocalBounds ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_metric_finite_borel_radon]:
    supporting Radon assertion for T(U), Federer
    3.3.4, p. 290. On an actual compact
    metric carrier, a finite Borel regular
    outer measure satisfies all Radon laws.
    The point a is a local metric witness. *)
Theorem compact_metric_finite_borel_radon (R:realType) (X:metricType R)
    (mu:set X->\bar R) (a:X):
  is_measure mu ->is_borel_regular_measure mu ->
  compact (@setT X) ->mu setT< +oo ->is_radon_measure mu.
Proof.
move=>hMu hB hCompact hFinite.
have hProper:metric_boundedly_compact X.
  move=>x r _; exact:(subclosed_compact (@metric_closed_ball_closed R X x r)
    hCompact (@subsetT _ _)).
have hClosed C:closed C ->measure_measurable mu C.
  move=>hC; exact:(borel_regular_borel_measurable hMu hB (closed_borel_set hC)).
constructor.
- exact:metric_hausdorff.
- exact:compact_space_locally_compact hCompact.
- move=>K _; exact:(le_lt_trans (measure_mono hMu (@subsetT _ K)) hFinite).
- exact:borel_regular_open_measurable hB.
- move=>U hU c hBound.
  rewrite leNgt; apply/negP=>hLower.
  have [q [hQ1 hQ2]]:=extended_rationals_order_dense hLower.
  have [K [hK [hKU hMass]]]:=structure_open_compact_inner_strict
    a hMu hProper hClosed hU hQ2.
  by have:=lt_le_trans (lt_trans hQ1 hMass) (hBound K hK hKU); rewrite ltxx.
- move=>A c hLower; exact:(finite_borel_regular_open_infimum hMu hB hFinite hLower).
Qed.
