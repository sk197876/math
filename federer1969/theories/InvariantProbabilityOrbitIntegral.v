(** Federer (1969), 3.2.48, p. 286: signed Fubini computes
    an invariant probability average. Finiteness of the actual source
    measure, rather than an additional uniform bound on the Jacobian,
    supplies the countable-measurability requirement of 2.6.2(4). *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasurePushforward
  BorelRegularMeasureUP CountableOpenBaseUP ProductMeasure ProductBorelRegularity
  FiniteRegularPushforwardIntegral PartialFunctionUP PartialFunctionPrecomposition
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality MeasureIntegralUniqueness
  MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP CountablyMeasurableUP
  CountablyMeasurableFunctions CountablyMeasurableBasic ExtendedRealOrderTopology CountablyMeasurableNullModification
  ProductFunctionFubini PartialProductSections ParameterizedIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_measure_function_countably_measurable]: the
    finite-source instance of the countable-measurability condition
    in 2.6.2(4), p. 115, used in 3.2.48, p. 286.
    Measurability of the actual nonzero locus is proved first. *)
Lemma finite_measure_function_countably_measurable (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu)
    (f:partial_function X (extended_real_line R)):
  mu setT< +oo ->is_measure_measurable_function mu f ->
  is_countably_measure_measurable_function mu (0:extended_real_line R) f.
Proof.
move=>hFinite hMeas; constructor; first exact hMeas.
apply:finite_measurable_set_countably_measurable.
- exact (measurable_function_nonzero_locus hm (@extended_real_zero_closed R) hMeas).
- exact (le_lt_trans (measure_mono hm (fun x _=>I)) hFinite).
Qed.

(** Source for [invariant_probability_orbit_integral]: the signed
    probability-averaging computation in 3.2.48, p. 286. The action
    is specified here by its previously proved full image-measure law.
    Its actual orbit integrals are finite almost everywhere. Their
    summable computed mean proves finiteness of the original integral;
    no separate joint, orbit or Jacobian summability premise is added. *)
Theorem invariant_probability_orbit_integral (R:realType) (G X:topologicalType)
    (alpha:set G->\bar R) (beta:set X->\bar R)
    (ha:is_measure alpha) (hb:is_measure beta)
    (U:nat->set G) (V:nat->set X) (F:G*X->X)
    (v mean:X->R) (q : \bar R) (b:R):
  is_countable_open_base U ->is_countable_open_base V ->
  is_borel_regular_measure alpha ->is_borel_regular_measure beta ->
  alpha setT= 1 ->beta setT< +oo ->
  measure_pushforward F (product_measure ha hb)=beta ->
  is_measure_integral beta (real_total_integrand v) q ->
  measure_almost_everywhere beta [set x|is_measure_integral alpha
    (real_total_integrand (fun g=>v (F (g,x)))) (mean x)%:E] ->
  is_measure_integral beta (real_total_integrand mean) b%:E ->q=b%:E.
Proof.
move=>hU hV hRA hRB hTotal hFinite hPush hIntegral hOrbits hMean.
pose rho:=product_measure ha hb.
have hr:=product_measure_is_measure ha hb.
have hReg:=product_measure_borel_regular ha hb hU hV hRA hRB.
have hWhole:(setT:set (G*X))=(setT:set G) `*` (setT:set X).
  by apply/seteqP; split=>z _; [split|exact I].
have hRhoFinite:rho setT< +oo.
  have hBound:=product_measure_rectangle_bound ha hb (@measure_measurable_whole R G alpha ha)
    (@measure_measurable_whole R X beta hb).
  rewrite -hWhole hTotal mul1e in hBound; exact (le_lt_trans hBound hFinite).
have hImageIntegral:is_measure_integral (measure_pushforward F rho) (real_total_integrand v) q.
  by rewrite hPush.
have hProduct:=(@finite_regular_pushforward_integral_iff R (G*X)%type X rho hr
  (borel_regular_is_regular hr hReg) F (real_total_integrand v) hRhoFinite q).2 hImageIntegral.
have hCount:=finite_measure_function_countably_measurable hr hRhoFinite hProduct.1.
have [_ hOuter]:=@product_function_fubini R G X alpha beta ha hb
  (partial_function_precompose F (real_total_integrand v)) q hProduct hCount.
have hAlmost:measure_almost_equal beta
    (parameterized_integral alpha (partial_product_horizontal_section
      (partial_function_precompose F (real_total_integrand v)))) (real_total_integrand mean).
  apply:(measure_almost_everywhere_mono hb _ hOrbits)=>x hOrbit.
  exists (mean x)%:E; split; last exact ((real_total_integrand_graph _ _ _).2 erefl).
  apply/parameterized_integral_specification.
  apply:(measure_integral_graph_equivalent _ hOrbit)=>g z.
  by [].
have hRestored:=measure_integral_almost_equal hb hOuter hAlmost.
exact (measure_integral_unique hRestored hMean).
Qed.
