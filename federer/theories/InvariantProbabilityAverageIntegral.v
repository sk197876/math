(** Federer (1969), 3.2.48, p. 286: averaging a signed
    integrable source function over the actual invariant probability
    action preserves its integral. Finite regular source measures prove
    completed composition measurability before image-measure transport. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasurePushforward
  BorelRegularMeasureUP CountableOpenBaseUP ProductMeasure ProductBorelRegularity
  InvariantProbabilityAverage MeasureIntegralUP PartialFunctionUP PartialFunctionPrecomposition
  ExtendedRealOrderTopology PushforwardMeasurableFunctions PushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [invariant_probability_average_integral]: the signed
    invariant averaging step in 3.2.48, p. 286. The original partial
    integrability domain and either infinite integral value are retained.
    No separate joint-composition or orbit-integrability premise is added. *)
Theorem invariant_probability_average_integral (R:realType) (G X:topologicalType)
    (alpha:set G->\bar R) (beta:set X->\bar R)
    (ha:is_measure alpha) (hb:is_measure beta)
    (U:nat->set G) (V:nat->set X) (F:G*X->X)
    (f:partial_function X (extended_real_line R)) a:
  is_countable_open_base U ->is_countable_open_base V ->
  is_borel_regular_measure alpha ->is_borel_regular_measure beta ->
  alpha setT= 1 ->beta setT< +oo ->continuous F ->
  (forall g,measure_pushforward (fun x=>F (g,x)) beta=beta) ->
  is_measure_integral beta f a ->
  is_measure_integral (product_measure ha hb) (partial_function_precompose F f) a.
Proof.
move=>hU hV hRA hRB hTotal hFinite hF hInvariant hIntegral.
have hPush:=@invariant_probability_average_pushforward R G X alpha beta ha hb U V F
  hU hV hRA hRB hTotal hFinite hF hInvariant.
pose rho:=product_measure ha hb.
have hr:=product_measure_is_measure ha hb.
have hReg:=product_measure_borel_regular ha hb hU hV hRA hRB.
have hWhole:(setT:set (G*X))=(setT:set G) `*` (setT:set X).
  by apply/seteqP; split=>z _; [split|exact I].
have hRhoFinite:rho setT< +oo.
  have hBound:=product_measure_rectangle_bound ha hb (@measure_measurable_whole R G alpha ha)
    (@measure_measurable_whole R X beta hb).
  rewrite -hWhole hTotal mul1e in hBound; exact (le_lt_trans hBound hFinite).
have hPushIntegral:is_measure_integral (measure_pushforward F rho) f a by rewrite hPush.
have hComposition:=@regular_pushforward_measurable_composition R (G*X)%type X
  (extended_real_line R) rho hr (borel_regular_is_regular hr hReg) F f hRhoFinite hPushIntegral.1.
exact ((@measure_pushforward_integral_iff R (G*X)%type X rho hr F f hComposition a).2 hPushIntegral).
Qed.
