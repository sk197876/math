(** Federer (1969), 3.2.7, p. 246:
    a putatively measurable bounded sine-weighted integrand
    is summable on the finite principal source branch.
    This supporting domination lemma retains actual partial
    domains and uses 2.4.9, p. 85. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionIntegralParts PartialAbsolutePartsGraph PartialExtendedOrderLoci
  CharacteristicFunctionUP MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasureIntegralUP MeasureExtendedCharacteristicIntegral MeasureIntegralGraphEquivalence MeasureAbsoluteSummability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_supported_partial_summable]: supporting
    restriction to a finite branch in the first example of
    Federer 3.2.7, p. 246. A measurable actual
    partial integrand dominated by a finite constant times
    a finite-measure characteristic function is summable. *)
Lemma bounded_supported_partial_summable (R:realType) (X:choiceType)
    (mu:set X->\bar R) (F:partial_function X (extended_real_line R))
    (A:set X) (chi:X->R) (M:R):
  is_measure mu -> measure_measurable mu A -> (mu A< +oo)%E ->
  is_characteristic_function A chi -> 0<=M -> is_measure_measurable_function mu F ->
  measure_almost_everywhere mu [set x|exists z:R,
    partial_function_graph F x z%:E /\ `|z|<=M*chi x] ->
  is_measure_summable mu F.
Proof.
move=>hm hA hAF hChi hM hMeas hBound.
have hFinite:mu A \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hm A)).
pose c:=fine (mu A).
have hc:mu A=c%:E by rewrite /c fineK.
pose H:=partial_function_total (fun x=>(M*chi x)%:E:extended_real_line R).
have hH:is_measure_integral mu H (M*c)%:E.
  have hi:=@measure_nonnegative_extended_characteristic_integral R X mu hm A chi M%:E hChi hA
    (ltac:(by rewrite lee_fin)).
  rewrite hc -EFinM in hi.
  apply:(measure_integral_graph_equivalent _ hi)=>x z.
  change ((M%:E*(chi x)%:E)%E=z <-> (M*chi x)%:E=z).
  by rewrite -EFinM.
have hDom:measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value F) H).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hBound)=>x [z [hz hb]].
  exists `|z|%:E,(M*chi x)%:E; split.
  - exists z%:E; split=>//; by rewrite abse_EFin.
  - split; first exact:erefl; by rewrite lee_fin.
exact ((measure_dominated_summable hm hMeas (ex_intro _ (M*c) hH) hDom).1).
Qed.
