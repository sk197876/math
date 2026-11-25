(** Federer (1969), 3.2.22(3), p. 260:
    characteristic approximation gives nonnegative
    weighted coarea from the proved subset identities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureIntegralUP
  WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion PositiveVanishingWeightsSealed
  CharacteristicFunctionUP CharacteristicFunctionSealed WeightedCharacteristicIntegral NonnegativeSum
  MappingMultiplicity CoareaCharacteristicExpansion MeasureTotalPositiveScale TotalNonnegativeSeriesIntegral
  ParameterizedIntegral ParameterizedIntegralLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_characteristic_expansion_supported]:
    supporting the standard approximation in Federer
    3.2.22, p. 260, using 2.3.3, p. 76.
    For a function zero outside W, every set in
    a positive-weight characteristic expansion lies in W.
    A positive summand outside W would contradict
    the zero value of the nonnegative sum. *)
Lemma positive_characteristic_expansion_supported (R:realType) (X:choiceType)
    (rho:set X->\bar R) (W:set X) (u:X->\bar R) (r:nat->R)
    (E:nat->set X) (s:nat->X->R):
  (forall j,(0<r j)%R) ->is_weighted_characteristic_expansion rho u r E s ->
  (forall x,~W x ->u x=0) ->forall j,E j `<=` W.
Proof.
move=>hr hExp hOff j x hx; apply:contrapT=>hNot.
have hTerm:=@nonnegative_sum_term R [the choiceType of (nat:Type)] setT
  (fun k=>(r k*s k x)%R%:E) j Logic.I.
rewrite (expansion_pointwise_sum hExp x)
  (characteristic_on_set (expansion_characteristic_laws hExp j) hx) mulr1 (hOff x hNot) lee_fin in hTerm.
have hFalse:=lt_le_trans (hr j) hTerm; by rewrite ltxx in hFalse.
Qed.

(** Source for [supported_coarea_nonnegative_integral]:
    the nonnegative standard approximation in Federer
    3.2.22(3), p. 260, following 3.2.12,
    p. 250. Source characteristic integrals and
    actual fibre characteristic integrals sum by 2.4.8.
    Each expansion set lies in W, so only the
    proved subset coarea identities on W are used.
    Inner integrability and outer measurability are
    conclusions, with infinite values retained. *)
Theorem supported_coarea_nonnegative_integral (R:realType) (X Y:choiceType)
    (rho nu beta:set X->\bar R) (alpha:set Y->\bar R)
    (hr:is_measure rho) (hn:is_measure nu) (hb:is_measure beta) (ha:is_measure alpha)
    (F:X->Y) (W:set X) (u:X->extended_real_line R):
  (forall A,measure_measurable rho A ->measure_measurable nu A) ->
  (forall A,A `<=` W ->measure_measurable rho A ->
    is_measure_integral alpha (partial_function_total (fun y=>(beta (mapping_fibre F A y):extended_real_line R))) (nu A)) ->
  (forall A,A `<=` W ->measure_measurable rho A ->
    measure_almost_everywhere alpha [set y|measure_measurable beta (mapping_fibre F A y)]) ->
  is_measure_measurable_function rho (partial_function_total u) ->
  (forall x,0<=u x) ->(forall x,~W x ->u x=0) ->
  exists a,is_measure_integral nu (partial_function_total u) a /\
    is_measure_integral alpha (parameterized_integral beta
      (fun y=>partial_function_zero_extension (0:extended_real_line R) [set x|F x=y]
        (partial_function_total u))) a.
Proof.
move=>hMeasTransfer hCharacteristic hFibre hu hNonnegative hOff.
pose r:=@PositiveVanishingWeights.value R.
have hWeights:=@PositiveVanishingWeights.laws R.
have hPositive:=expansion_weights_positive hWeights.
have [E [s [hExp _]]]:=@measurable_weighted_characteristic_expansion R X rho hr u r hu hNonnegative hWeights.
have hSupport:=positive_characteristic_expansion_supported hPositive hExp hOff.
have hNuExp:is_weighted_characteristic_expansion nu u r E s.
  constructor.
  - move=>j; exact:(hMeasTransfer _ (expansion_sets_measurable hExp j)).
  - exact:expansion_characteristic_laws hExp.
  - exact:expansion_pointwise_sum hExp.
pose theta j y:extended_real_line R:=beta (mapping_fibre F (E j) y).
have hTheta j:is_measure_integral alpha (partial_function_total (theta j)) (nu (E j)).
  exact:(hCharacteristic (E j) (hSupport j) (expansion_sets_measurable hExp j)).
have hScaled j:is_measure_integral alpha (partial_function_total (fun y=>(r j)%:E*theta j y))
    ((r j)%:E*nu (E j)).
  exact:(measure_total_positive_scale_integral ha (hPositive j) (hTheta j)).
have hScaledPositive j y:0<=(r j)%:E*theta j y.
  apply:mule_ge0; first by rewrite lee_fin; exact:ltW (hPositive j).
  exact:(measure_nonnegative hb _).
have hOuter:=total_nonnegative_series_integral ha hScaledPositive hScaled.
have hInner:=coarea_characteristic_expansion_inner_integral hb ha hPositive hExp
  (fun j=>hFibre (E j) (hSupport j) (expansion_sets_measurable hExp j)).
exists (nonnegative_sum setT (fun j=>(r j)%:E*nu (E j))); split.
- exact:(weighted_characteristic_expansion_integral hn hPositive hNuExp).
- exact:(parameterized_integral_total_outer_transfer ha hInner hOuter).
Qed.
