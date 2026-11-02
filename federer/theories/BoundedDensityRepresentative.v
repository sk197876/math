(** Federer (1969), 2.5.10, p. 101: choosing local densities with a common
    pointwise bound before disjoint gluing. The essential bound comes from
    2.5.7(ii), p. 98; modification on a null set is permitted by 2.3.2, p.
    73, and 2.4.3(2), p. 81. Replacing values exceeding the bound by zero
    keeps the original support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableTotalBasic SummableRealFunctionUP MeasureIntegralAlmostEquality
  TotalScalarLpUP TotalScalarLpCharacteristic TotalScalarComparison LinfinitySequenceEnvelope
  TotalEssentialNormBound LpFunctionalDensityUP CharacteristicFunctionSealed TotalScalarCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lp_density_pointwise_bounded_representative]: supporting
    bounded-representative step for Federer 2.5.10, p. 101 Full local
    L-infinity membership and every actual integral formula survive. *)
Lemma lp_density_pointwise_bounded_representative (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : (X -> R) -> R) (k : X -> R) (M : R) :
  (0 <= M)%R -> is_lp_functional_density mu 1 +oo A k -> total_scalar_lp_norm mu +oo k <= M%:E ->
  exists l : X -> R, is_lp_functional_density mu 1 +oo A l /\ forall x, (`|l x| <= M)%R.
Proof.
move=> hM hk hb.
pose E := [set x | (`|k x| <= M)%R].
have ha := @total_essential_norm_almost_bound R X mu hm k M hk.1 hb.
have habs := @total_scalar_lp_absolute R X mu hm +oo k hk.1.
have hc := @measurable_total_constant R X
  [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm M.
have hE : measure_measurable mu E := @total_scalar_measurable_comparison R X mu hm
  (fun x => `|k x|%R) (fun _ => M) habs.2.1 hc.
pose l := total_scalar_cutoff E k.
have hl : total_scalar_lp mu +oo l.
  exact: (@total_scalar_lp_characteristic_piece R X mu hm +oo E _ k
    (@CharacteristicFunction.laws R X E) hE hk.1).
exists l; split.
- split=> // f hf; apply: (@measure_integral_almost_equal R X mu hm _ _ _ (hk.2 f hf)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ ha)=> x hx.
  exists (f x * k x)%R%:E; split; first by apply/real_total_integrand_graph.
  apply/real_total_integrand_graph; by rewrite /l (total_scalar_cutoff_on k hx).
- move=> x; case: (pselect (E x))=> hx.
  + by rewrite /l (total_scalar_cutoff_on k hx).
  + by rewrite /l (total_scalar_cutoff_off k hx) normr0.
Qed.
