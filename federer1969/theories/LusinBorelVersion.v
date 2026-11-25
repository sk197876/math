(** Federer (1969), 2.3.6, p. 77, first corollary of
    Lusin's theorem. Sources: ContinuousClosedPieceBorel.v.
    The total Borel representative needs an inhabited target if
    X is nonempty, just as the extension remark of 2.3.2 does.
    This local boundary qualification is not in Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialContinuityUP
  MeasureUP MeasureAlmostUP MeasurableFunctionUP CountablyMeasurableUP
  BorelFunctionUP BorelRegularMeasureUP RadonMeasureUP LusinMetric LusinRadon
  LusinClosedExhaustion BorelVersionFromClosedCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_borel_version_metric]: direct first corollary
    of Federer 2.3.6, p. 77, in the metric/Borel-regular case.
    A supplied target point records the necessary nonempty-target
    qualification for the total representative. *)
Theorem lusin_borel_version_metric (R : realType) (X Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu)
    (D : set Y) (f : partial_function X Y) (y0 : Y) :
  countable D -> dense D -> is_measure_measurable_function mu f ->
  measure_countably_measurable mu setT -> exists h : X -> Y,
    is_borel_function h /\ measure_almost_equal mu f (partial_function_total h).
Proof.
move=> hc hd hf hcnt.
have [C [hC [hcont hnull]]] := @lusin_closed_exhaustion R X Y mu hm f hcnt
  (fun A hA hfin e he => @lusin_borel_regular R X Y mu hm hr D A f e hc hd hf hA hfin he).
exact (@borel_version_from_closed_cover R X Y [the countType of ((nat * nat)%type : Type)]
  mu hm f y0 C hC hcont hnull).
Qed.

(** Source for [lusin_borel_version_radon]: direct first corollary
    of Federer 2.3.6, p. 77, in the locally compact Hausdorff
    Radon case. Compact Lusin pieces are closed by Hausdorff separation. *)
Theorem lusin_borel_version_radon (R : realType) (X : topologicalType) (Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (D : set Y) (f : partial_function X Y) (y0 : Y) :
  countable D -> dense D -> is_measure_measurable_function mu f ->
  measure_countably_measurable mu setT -> exists h : X -> Y,
    is_borel_function h /\ measure_almost_equal mu f (partial_function_total h).
Proof.
move=> hc hd hf hcnt.
have happ A : measure_measurable mu A -> mu A < +oo -> forall e : R, (0 < e)%R ->
    exists C, closed C /\ C `<=` A /\ mu (A `\` C) < e%:E /\ partial_function_continuous_on C f.
  move=> hA hfin e he.
  have [C [hC [hCA [herr hcont]]]] := @lusin_radon R X Y mu hm hr D A f e hc hd hf hA hfin he.
  exists C; split; first exact: compact_closed (radon_hausdorff hr) hC.
  by split=> //; split.
have [C [hC [hcont hnull]]] := @lusin_closed_exhaustion R X Y mu hm f hcnt happ.
exact (@borel_version_from_closed_cover R X Y [the countType of ((nat * nat)%type : Type)]
  mu hm f y0 C hC hcont hnull).
Qed.
