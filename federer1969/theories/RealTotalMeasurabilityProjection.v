(** Federer (1969), 4.1.1, p. 346: a finite
    locally integrable dual norm is measurable
    as a real function. This supporting adapter
    uses the existing Borel finite-part projection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic MeasureUP
  MeasurableFunctionUP MeasurableGraphEquivalence SummableRealFunctionUP TotalScalarMeasurability ExtendedLatticeDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [real_total_measurability_projection]: finite
    real integrands have real-line measurability,
    supporting the original local norm condition
    in Federer 4.1.1, p. 346. *)
Lemma real_total_measurability_projection (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (f:X->R):
  is_measure_measurable_function mu (real_total_integrand f) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_line_metric R))).
Proof.
move=>hf.
have hExtended:is_measure_measurable_function mu
  (partial_function_total (fun x=>((f x)%:E:extended_real_line R))).
  apply:(@measurable_function_graph_equivalent R X (extended_real_line R) mu (real_total_integrand f) _ _ hf).
  move=>x y; exact:real_total_integrand_graph.
have hFine:=fine_density_measurable hm hExtended.
have hEq:(fun x=>fine ((f x)%:E))=f by apply:funext=>x.
rewrite hEq in hFine; exact (@total_scalar_real_measurable R X mu hm f hFine).
Qed.
