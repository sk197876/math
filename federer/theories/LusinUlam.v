(** Federer (1969), 2.3.6, p. 77, final paragraph:
    metric and Radon forms with a Ulam-dense target. Source
    editions and exact support argument: MeasurableFiniteImageSupport.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialContinuityUP MeasureUP MeasurableFunctionUP
  BorelRegularMeasureUP RadonMeasureUP UlamCardinalUP LusinMetric LusinRadon
  LusinApproximationUP LusinUlamRange.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_borel_regular_ulam_dense]: direct extension
    of the metric case of Lusin's theorem in Federer 2.3.6,
    p. 77. Separability is replaced by the stated Ulam condition. *)
Theorem lusin_borel_regular_ulam_dense (R : realType) (X Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_borel_regular_measure mu)
    (D : set Y) (A : set X) (f : partial_function X Y) (e : R) :
  dense D -> is_ulam_set R D -> is_measure_measurable_function mu f ->
  measure_measurable mu A -> mu A < +oo -> (0 < e)%R ->
  exists C, closed C /\ C `<=` A /\ mu (A `\` C) < e%:E /\ partial_function_continuous_on C f.
Proof.
move=> hd hu hf hA hfin he.
have hL : has_lusin_approximation mu (@closed X).
  move=> Z H hc hH F hF B hB hfinB delta hdelta.
  exact (@lusin_borel_regular R X Z mu hm hr H B F delta hc hH hF hB hfinB hdelta).
exact (@lusin_ulam_dense_range R X Y mu hm (@closed X) D A f e closed0 hL hd hu hf hA hfin he).
Qed.

(** Source for [lusin_radon_ulam_dense]: direct extension of
    the compact Radon case in Federer 2.3.6, p. 77.
    The original function, not only an almost-equal modification,
    is continuous at every point of the final compact set. *)
Theorem lusin_radon_ulam_dense (R : realType) (X : topologicalType) (Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (D : set Y) (A : set X) (f : partial_function X Y) (e : R) :
  dense D -> is_ulam_set R D -> is_measure_measurable_function mu f ->
  measure_measurable mu A -> mu A < +oo -> (0 < e)%R ->
  exists C, compact C /\ C `<=` A /\ mu (A `\` C) < e%:E /\ partial_function_continuous_on C f.
Proof.
move=> hd hu hf hA hfin he.
have hL : has_lusin_approximation mu (@compact X).
  move=> Z H hc hH F hF B hB hfinB delta hdelta.
  exact (@lusin_radon R X Z mu hm hr H B F delta hc hH hF hB hfinB hdelta).
exact (@lusin_ulam_dense_range R X Y mu hm (@compact X) D A f e compact0 hL hd hu hf hA hfin he).
Qed.
