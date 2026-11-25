(** Federer (1969), 4.1.7, p. 359:
    the original L1 extension for the weighted
    image measure can be pulled back to
    its source measure. This supporting finite-p
    isometry is the original norm formula
    2.4.12, p. 86, and image integral
    formula 2.4.18, pp. 90–91. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionPrecomposition PartialNormPower
  MeasureUP MeasurePushforward MeasureAlmostUP RadonMeasureUP CountablyMeasurableUP
  MeasurableFunctionUP MeasurableGraphEquivalence MeasurableNormedFunctionUP MeasurableNormPower
  MeasureLpNormUP MeasureLpNorm MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureIntegralGraphEquivalence PushforwardIntegral RadonImagePartialMeasurability
  PartialNormedArithmetic MeasureAlmostBasic MeasureLpConvergence MeasureLpDifferenceMembership MeasureLpNormAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RadonImageLpPullback.
Variable R:realType.
Variables X Y:topologicalType.
Variable Z:lmodType R.
Variable N:Z->R.
Hypothesis hN:is_real_norm N.
Local Notation ZT := (real_norm_metric_space hN).
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable f:X->Y.
Hypothesis hf:continuous f.
Local Notation nu := (measure_pushforward f mu).
Let hn:=@measure_pushforward_is_measure R X Y f mu hm.
Hypothesis hs:is_radon_measure nu.
Variable D:set ZT.
Hypothesis hCount:countable D.
Hypothesis hDense:dense D.
Hypothesis hCountable:measure_countably_measurable nu setT.

(** Source for [radon_image_lp_pullback]:
    pulling an original Lp(nu) partial field
    back by f gives an Lp(mu)
    field with exactly the same norm,
    supporting the L1 uniqueness argument of
    Federer 4.1.7, p. 359. All
    original conull domains remain partial. *)
Theorem radon_image_lp_pullback p (g:partial_function Y ZT):
  is_measure_lp_function nu p g->
  is_measure_lp_function mu p (partial_function_precompose f g) /\
    measure_lp_norm mu N p (partial_function_precompose f g)=measure_lp_norm nu N p g.
Proof.
move=>hG.
pose pull:=partial_function_precompose f g.
have hMeas:=@radon_image_partial_measurable_precompose R X Y ZT mu hm hr f hf hs D 0 g
  hCount hDense hCountable hG.2.1.1.
have hPower:=@measurable_norm_positive_power R X Z N hN mu hm p pull
  (lt_le_trans ltr01 hG.1) hMeas.
have hGraph x z:partial_function_graph (partial_function_precompose f (partial_norm_power N p g)) x z<->
    partial_function_graph (partial_norm_power N p pull) x z.
  exact:partial_function_precompose_postcompose.
have hPowerPre:=measurable_function_graph_equivalent (fun x z=>iff_sym (hGraph x z)) hPower.
have [_ [b [hIntegral hValue]]]:=@measure_lp_norm_specification R Y Z N hN nu p g hn hG.1 hG.2.1.1.
have hSource:=(@measure_pushforward_integral_iff R X Y mu hm f (partial_norm_power N p g)
  hPowerPre b).2 hIntegral.
have hPullIntegral:=measure_integral_graph_equivalent hGraph hSource.
have hNorm:measure_lp_norm mu N p pull=measure_lp_norm nu N p g.
  exact:(eq_trans (@measure_lp_norm_of_integral R X Z N hN mu p pull b hm hG.1 hMeas hPullIntegral)
    (esym hValue)).
have hFinite:(measure_lp_norm mu N p pull < +oo)%E by rewrite hNorm;exact:hG.2.2.1.
split;last exact:hNorm.
split;first exact:hG.1.
split.
- split;first exact:hMeas.
  have [A [hA hNull]]:=hG.2.1.2.
  exists A;split;first exact:hA.
  by rewrite /pull partial_function_precompose_preimage.
- split;first exact:hFinite.
  exact:(@finite_lp_norm_countably_measurable R X Z N hN mu hm p pull hG.1 hMeas hFinite).
Qed.
(** Source for [radon_image_lp_pullback_distance]:
    the same original pullback preserves the
    full difference seminorm, supporting the
    one-Lipschitz L1 image integral in
    Federer 4.1.7, p. 359. Both
    partial domains are retained. *)
Theorem radon_image_lp_pullback_distance p (a b:partial_function Y ZT):
  is_measure_lp_function nu p a->is_measure_lp_function nu p b->
  measure_lp_distance mu N p (partial_function_precompose f a) (partial_function_precompose f b)=
    measure_lp_distance nu N p a b.
Proof.
move=>ha hb.
have [hAP _]:=radon_image_lp_pullback ha.
have [hBP _]:=radon_image_lp_pullback hb.
have hDifference:=@measure_lp_function_subtract R Y Z N hN nu hn p a b ha hb.
have [hPreDifference hNorm]:=radon_image_lp_pullback hDifference.
have hDifferencePre:=@measure_lp_function_subtract R X Z N hN mu hm p
  (partial_function_precompose f a) (partial_function_precompose f b) hAP hBP.
have hDomains:=measure_almost_everywhere_and hm
  (measurable_function_domain hAP.2.1.1) (measurable_function_domain hBP.2.1.1).
have hEqual:measure_almost_equal mu
    (partial_function_precompose f (partial_vector_subtract a b))
    (partial_vector_subtract (partial_function_precompose f a) (partial_function_precompose f b)).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hDomains)=>x [[u hu] [v hv]].
  exists (u-v);split.
  - change (partial_function_graph (partial_vector_subtract a b) (f x) (u-v)).
    apply/partial_vector_subtract_graph;exists u,v;by split=>//;split.
  - apply/partial_vector_subtract_graph;exists u,v;by split=>//;split.
have hNormEqual:=@measure_lp_norm_almost_equal R X Z N hN mu hm p _ _ ha.1
  hPreDifference.2.1.1 hDifferencePre.2.1.1 hEqual.
exact:(eq_trans (esym hNormEqual) hNorm).
Qed.
End RadonImageLpPullback.
