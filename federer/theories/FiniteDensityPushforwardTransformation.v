(** Federer (1969), 3.2.6, pp. 245–246: assemble
    speed density, the finite image measure and finite
    multiplicity density. All intermediate laws are explicit
    premises here and proved for the curve application below. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialDensityProduct MeasureUP MeasureAlmostUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasurePushforward BorelRegularMeasureUP CountablyMeasurableUP
  CountablyMeasurableBasic MeasureSplit MeasureDensityUP MeasurableFunctionUP
  FiniteDensityIntegralTransformation FiniteRegularPushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_density_pushforward_real_weight_iff]:
    supporting assembly of the arbitrary-weight identity in
    Federer 3.2.6, p. 245. The two densities and
    their pushforward agreement are hypotheses of this helper,
    not new project axioms. Both actual integral graphs are
    preserved, including undefined signed infinity differences. *)
Theorem finite_density_pushforward_real_weight_iff (R:realType) (X Y:metricType R)
    (mu nu:set X->\bar R) (beta xi:set Y->\bar R)
    (hm:is_measure mu) (hn:is_measure nu) (hb:is_measure beta) (hi:is_measure xi)
    (hr:is_borel_regular_measure mu) (hs:is_borel_regular_measure nu)
    (ht:is_borel_regular_measure beta) (hu:is_borel_regular_measure xi)
    (f:X->Y) (h:partial_function X (extended_real_line R)) (N:partial_function Y (extended_real_line R))
    (g:Y->real_line_metric R):
  is_measure_density mu h nu -> is_measure_measurable_function mu h ->
  measure_almost_everywhere mu [set x|exists r:R,(0<=r)%R /\ partial_function_graph h x r%:E] ->
  is_measure_density beta N xi -> is_measure_measurable_function beta N ->
  measure_almost_everywhere beta [set y|exists r:R,(0<=r)%R /\ partial_function_graph N y r%:E] ->
  nu setT< +oo -> xi setT< +oo -> xi=measure_pushforward f nu -> forall a,
  is_measure_integral mu (partial_density_product
    (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R)) h) a <->
  is_measure_integral beta (partial_density_product
    (partial_function_total (fun y=>(g y)%:E:extended_real_line R)) N) a.
Proof.
move=>hNu hH hHF hXi hN hNF hNuFin hXiFin hEq a.
have hNuCount:=finite_measurable_set_countably_measurable (measure_measurable_whole hn) hNuFin.
have hXiCount:=finite_measurable_set_countably_measurable (measure_measurable_whole hi) hXiFin.
have hSrc:=@finite_density_arbitrary_real_weight_integral_iff R X mu nu hm hr hs h
  (fun x=>g (f x)) hNu hH hHF hNuCount a.
have hTgt:=@finite_density_arbitrary_real_weight_integral_iff R Y beta xi hb ht hu N g
  hXi hN hNF hXiCount a.
pose u:=partial_function_total (fun y=>(g y)%:E:extended_real_line R).
have hPush:=@finite_regular_pushforward_integral_iff R X Y nu hn
  (borel_regular_is_regular hn hs) f u hNuFin a.
rewrite -hEq in hPush.
have hGraphs x z:partial_function_graph (partial_function_precompose f u) x z <->
    partial_function_graph (partial_function_total (fun x=>(g (f x))%:E:extended_real_line R)) x z.
  exact (partial_function_precompose_total f _ x z).
split=>hInt.
- have hS:=hSrc.2 hInt.
  have hPre:=measure_integral_graph_equivalent (fun x z=>iff_sym (hGraphs x z)) hS.
  exact (hTgt.1 (hPush.1 hPre)).
- have hT:=hTgt.2 hInt.
  have hPre:=hPush.2 hT.
  exact (hSrc.1 (measure_integral_graph_equivalent hGraphs hPre)).
Qed.
