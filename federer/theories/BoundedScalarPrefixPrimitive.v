(** Federer (1969), 3.2.33, p. 270: existence
    of the scalar primitive defined by integration from zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureSubsetIntegral MeasurableFunctionUP LebesgueScalarMeasure BorelRegularMeasureUP
  TopologicalBorel IntervalBumpFunctions UnitBoundedSubsetIntegralFinite.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_scalar_prefix_primitive_exists]: the
    definition g(t)= integral from zero to t of psi in
    Federer 3.2.33, p. 270. Bounded measurability proves
    every finite interval integral exists before choosing local
    real values. Outside [0,1] the total representative is
    auxiliary and carries no asserted primitive identity. *)
Lemma bounded_scalar_prefix_primitive_exists (R:realType) (psi:R->R):
  is_measure_measurable_function (@lebesgue_scalar_measure R)
    (partial_function_total (fun t:real_line_metric R=>((psi t)%:E:extended_real_line R))) ->
  (forall t,0<=psi t<= 1) ->exists g:R->R,forall t,0<=t<= 1 ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,t]
      (partial_function_total (fun t:real_line_metric R=>((psi t)%:E:extended_real_line R))) (g t)%:E.
Proof.
move=>hPsi hBounds.
have hm:=lebesgue_scalar_is_measure R.
have hExists t:exists r:R,0<=t<= 1 ->is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,t]
    (partial_function_total (fun t:real_line_metric R=>((psi t)%:E:extended_real_line R))) r%:E.
  have [ht|ht]:=pselect (0<=t<= 1); last by exists 0=>h; exfalso; exact:ht h.
  have hSet:measure_measurable (@lebesgue_scalar_measure R) `[0,t].
    apply:(@borel_regular_borel_measurable R (real_line_metric R) (@lebesgue_scalar_measure R)
      hm (lebesgue_scalar_borel_regular R) `[0,t]).
    exact:(closed_borel_set (@segment_closed_real R 0 t)).
  have hMass:=lebesgue_scalar_segment (andP ht).1.
  have hFinite:(@lebesgue_scalar_measure R (`[0%R,t]:set (real_line_metric R))< +oo)%E by rewrite hMass; exact:ltry.
  have hExtended s:((0: \bar R)<=(psi s)%:E<= 1)%E.
    by rewrite !lee_fin; exact:hBounds.
  have [r [hI _]]:=unit_bounded_nonnegative_subset_integral_finite hm hSet hFinite hPsi hExtended.
  by exists r.
have [g hG]:=choice hExists; by exists g.
Qed.
