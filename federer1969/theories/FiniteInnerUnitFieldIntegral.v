(** Federer (1969), 3.2.27, p. 263: integrate
    the finite-dimensional field Xi of norm one. The
    finite-source L1 membership and vector integral are
    consequences of 2.4.12, pp. 86–88, not extra
    assumptions about the rectifiable set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  RealNormUP NormMetric LinearBasis FiniteNormMetricPolish
  PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition PartialNormPower RealPower
  ExtendedRealOrderTopology MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableNormedFunctionUP SeparableTargetNormedMeasurability
  FiniteMeasureBoundedNorm MeasureLpMembershipUP MeasureLpNorm MeasureLoneNormIntegral
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureIntegralUniqueness
  MeasureVectorIntegralUP MeasureVectorIntegral MeasureVectorIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_inner_unit_field_vector_integral]: the
    vector integral and the equality integral |Xi|=H^m(W)
    used in 3.2.27, p. 263. A finite orthonormal
    basis is unnecessary here; any finite basis suffices.
    The partial domain is conull for the actual finite
    source measure. No outside value is supplied. *)
Theorem finite_inner_unit_field_vector_integral (R:realType) (X:choiceType)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B)
    (I:finType) (e:I->V) (mu:set X->\bar R)
    (f:partial_function X (real_norm_metric_space (inner_norm_real_norm hB))):
  is_basis e ->is_measure mu ->mu setT < +oo ->
  is_measure_measurable_function mu f ->
  (forall x v,partial_function_graph f x v ->inner_norm hB v= 1%R) ->
  exists y:V,is_measure_vector_integral mu f y /\
    (inner_norm hB y)%:E<=mu setT /\
    measure_lp_norm mu (inner_norm hB) 1%R f=mu setT.
Proof.
move=>hBasis hMu hFinite hF hUnit.
pose N:=inner_norm hB.
pose hN:=inner_norm_real_norm hB.
have hOrdinal:is_basis (fun i:'I_(#|I|)=>e (enum_val i)).
  exact:(@basis_reindex R (Choice.clone I _) (Choice.clone 'I_(#|I|) _) V e
    hBasis enum_rank enum_val (@enum_rankK I) (@enum_valK I)).
have hComplete:=@finite_norm_metric_complete R V N hN #|I| (fun i=>e (enum_val i)) hOrdinal.
have [D [hD hDense]]:=@finite_norm_metric_separable R V N hN #|I| (fun i=>e (enum_val i)) hOrdinal.
have hFM:=@separable_target_measurable_normed R X V N hN D mu hMu f hD hDense hF.
have hFin:mu setT \is a fin_num by rewrite (ge0_fin_numE (measure_nonnegative hMu setT)).
pose a:R:=fine (mu setT).
have hMass:mu setT=a%:E by rewrite /a fineK.
have hBound:measure_almost_everywhere mu
    (partial_function_preimage f [set v|(N v<=1)%R]).
  apply:(measure_almost_everywhere_mono hMu _ (measurable_function_domain hF))=>x [v hv].
  exists v; split; first exact hv.
  change (is_true (inner_norm hB v<=1)%R); by rewrite (hUnit x v hv).
have hL1:=@finite_measure_bounded_norm_lp_one R X V N hN mu hMu a 1%R f hMass hFM hBound.
have hNormIntegral:=@measure_lone_norm_integral R X V N hN mu hMu f hL1.
have hConstant:=@finite_measure_constant_integral R X mu hMu a 1%R hMass.
rewrite mul1r in hConstant.
have hUnitIntegral:is_measure_integral mu (partial_norm_power N 1%R f) (mu setT).
  rewrite hMass.
  apply:(@measure_integral_almost_equal R X mu hMu _ _ _ hConstant).
  apply:(measure_almost_everywhere_mono hMu _ (measurable_function_domain hF))=>x [v hv].
  exists 1; split; first reflexivity.
  exists v; split; first exact hv.
  by rewrite /N (hUnit x v hv) real_power_one_base.
have hNormValue:measure_lp_norm mu N 1%R f=mu setT.
  exact:(measure_integral_unique hNormIntegral hUnitIntegral).
pose y:=@measure_vector_integral R X V N hN hComplete mu hMu f hL1.
have hY:=@measure_vector_integral_specification R X V N hN hComplete mu hMu f hL1.
exists y; split; first exact hY; split; last exact hNormValue.
rewrite -hNormValue; exact:(@measure_vector_integral_norm_bound R X V N hN mu hMu f y hY).
Qed.
