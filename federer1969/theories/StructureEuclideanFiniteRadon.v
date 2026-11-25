(** Federer (1969), 3.3.7, p. 294: the actual finite
    Borel regular projection measure is Radon on Euclidean space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanClosedBallCompact
  EuclideanAdditiveGroup MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  RadonMeasureUP MetricClosedBalls LipschitzFunctionCompact StructureOpenCompactInner
  FiniteBorelOpenInfimum ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_euclidean_finite_borel_radon]: the Radon
    assertion for psi in Federer 3.3.7, p. 294. Actual compact closed
    Euclidean balls and local compactness, together with finite Borel
    regularity, give all six laws of 2.2.5, pp. 62–63. Open compact
    inner approximation and the proved finite open-infimum law retain
    the original outer measure on every set. This includes R^0. *)
Theorem structure_euclidean_finite_borel_radon (R:realType) n
    (mu:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R):
  is_measure mu ->is_borel_regular_measure mu ->(mu setT< +oo)%E ->
  is_radon_measure mu.
Proof.
move=>hMu hBorel hFinite.
have hProper:metric_boundedly_compact (inner_metric_space (@euclidean_inner_productP R n)).
  move=>x r hr; exact:(@euclidean_closed_metric_ball_compact R n x r).
have hClosed C:closed C ->measure_measurable mu C.
  move=>hC; exact:(borel_regular_borel_measurable hMu hBorel (closed_borel_set hC)).
constructor.
- exact:metric_hausdorff.
- exact:(@euclidean_locally_compact R n).
- move=>K _; exact:(le_lt_trans (measure_mono hMu (@subsetT _ K)) hFinite).
- exact:borel_regular_open_measurable hBorel.
- move=>U hU c hBound.
  rewrite leNgt; apply/negP=>hLower.
  have [q [hQ1 hQ2]]:=extended_rationals_order_dense hLower.
  have [K [hK [hKU hMass]]]:=@structure_open_compact_inner_strict R
    (inner_metric_space (@euclidean_inner_productP R n)) mu 0 U (ratr q)
    hMu hProper hClosed hU hQ2.
  by have:=lt_le_trans (lt_trans hQ1 hMass) (hBound K hK hKU); rewrite ltxx.
- move=>A c hLower; exact:(finite_borel_regular_open_infimum hMu hBorel hFinite hLower).
Qed.
