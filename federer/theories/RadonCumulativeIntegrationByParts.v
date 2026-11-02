(** Federer (1969), 2.6.7, printed p. 121: the complete integration-by-parts
    identity for two Radon measures on R. The proof uses the printed
    triangle and Fubini, retaining atoms and both half-open endpoint
    conventions. The degenerate interval is included as a harmless
    strengthening. There is no correction to p. 121 in the local Federer
    erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CountableOrderIntervals
  MeasureUP MeasureFiniteClosure RadonMeasureUP MeasureIntegralUP SummableRealFunctionUP
  CumulativeFunctionPairUP CumulativeIntegrationByParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [radon_cumulative_integration_by_parts]: the
    displayed formula of Federer 2.6.7, p. 121. Both
    integrals are finite; zero extension expresses integration
    over the printed sets (a,b] and [a,b), respectively. *)
Theorem radon_cumulative_integration_by_parts (R : realType)
    (alpha beta : set R -> \bar R) (ha : is_measure alpha) (hb : is_measure beta)
    (hRa : @is_radon_measure R [the topologicalType of real_line_metric R] alpha)
    (hRb : @is_radon_measure R [the topologicalType of real_line_metric R] beta)
    (a b : R) (f g : R -> R) :
  a <= b -> is_cumulative_function_pair alpha beta a b f g ->
  exists I J : R,
    is_measure_integral beta (real_total_integrand (right_half_open_integrand a b f)) I%:E /\
    is_measure_integral alpha (real_total_integrand (left_half_open_integrand a b g)) J%:E /\
    I+J=f b*g b-f a*g a.
Proof.
move=> hab hfg.
have hAr t : measure_measurable alpha [set x | x < t].
  apply: (radon_open_measurable hRa).
  have ho : open ([set x : R | x < t] : set R^o) := order_strict_lower_ray_open t.
  exact: ho.
have hBr t : measure_measurable beta [set x | x <= t].
  have hO : measure_measurable beta [set x | t < x].
    apply: (radon_open_measurable hRb).
    have ho : open ([set x : R | t < x] : set R^o) := order_strict_upper_ray_open t.
    exact: ho.
  have he : [set x : R | x <= t]=~` [set x : R | t < x].
    apply/seteqP; split=> x /=.
    - move=> hxt; apply/negP; by rewrite -leNgt.
    - move=> /negP htx; by rewrite leNgt.
  rewrite he; exact: measure_measurable_complement hO.
exact (@cumulative_integration_by_parts R alpha beta ha hb a b f g
  hAr hBr hab (cumulative_lower_open_law hfg) (cumulative_lower_closed_law hfg)).
Qed.

(** Source for [radon_cumulative_integration_by_parts_exists]:
    existence and identity for the finite cumulative functions
    of Federer 2.6.7, p. 121. Finiteness at b implies
    the printed finiteness throughout [a,b] by monotonicity. *)
Corollary radon_cumulative_integration_by_parts_exists (R : realType)
    (alpha beta : set R -> \bar R) (ha : is_measure alpha) (hb : is_measure beta)
    (hRa : @is_radon_measure R [the topologicalType of real_line_metric R] alpha)
    (hRb : @is_radon_measure R [the topologicalType of real_line_metric R] beta)
    (a b : R) :
  a <= b -> (alpha [set t | (t < b)%R] < +oo)%E -> (beta [set t | (t <= b)%R] < +oo)%E ->
  exists f g : R -> R, exists I J : R,
    is_cumulative_function_pair alpha beta a b f g /\
    is_measure_integral beta (real_total_integrand (right_half_open_integrand a b f)) I%:E /\
    is_measure_integral alpha (real_total_integrand (left_half_open_integrand a b g)) J%:E /\
    I+J=f b*g b-f a*g a.
Proof.
move=> hab hA hB.
have [f [g hfg]] := @cumulative_function_pair_exists R alpha beta ha hb a b hA hB.
have [I [J [hI [hJ hIJ]]]] := @radon_cumulative_integration_by_parts R alpha beta ha hb hRa hRb a b f g hab hfg.
exists f,g,I,J; by split=> //; split=> //; split.
Qed.
