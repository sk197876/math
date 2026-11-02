(** Federer (1969), 3.2.6, pp. 245–246:
    actual differentiation almost everywhere follows from
    2.9.22 for the finite Euclidean target. This supporting
    finite-dimensional adapter uses abstract dual/bidual laws
    and the proved reflexivity result of 2.4.12. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis CompleteMetricUP
  ContinuousDualUP ContinuousDualNorm ContinuousDualSealed ContinuousBidualUP ContinuousBidualSealed
  FiniteContinuousReflexivity ReflexiveBVDifferentiation NormedCurveDerivativeUP CurveArcLength
  MeasureUP MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_bv_curve_derivative_almost]: supporting
    actual derivative existence for Federer 3.2.6, p. 245,
    by 2.9.22 and finite-dimensional reflexivity 2.4.12.
    All selected dual and bidual implementations remain opaque. *)
Theorem finite_norm_bv_curve_derivative_almost (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) n (e:'I_n->V) (he:is_basis e)
    (f:R->real_norm_metric_space hN):
  is_complete_metric_space (real_norm_metric_space hN) -> curve_locally_finite_variation f ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x|exists v:V,has_normed_curve_derivative N f x v].
Proof.
move=>hComplete hBV.
pose D:=@ContinuousDual.space R V N hN.
pose ed:=@ContinuousDual.evaluation R V N hN.
pose DN:=@ContinuousDual.norm R V N hN.
have hD:is_continuous_dual hN ed DN:=@ContinuousDual.laws R V N hN.
pose hDN:=continuous_dual_norm_is_norm hD.
pose B:=@ContinuousDual.space R D DN hDN.
pose eb:=@ContinuousDual.evaluation R D DN hDN.
pose BN:=@ContinuousDual.norm R D DN hDN.
have hB:is_continuous_dual hDN eb BN:=@ContinuousDual.laws R D DN hDN.
pose tau:=@ContinuousBidual.value R V D B N hN ed DN hD eb BN hB.
have ht:is_bidual_embedding ed eb tau:=@ContinuousBidual.laws R V D B N hN ed DN hD eb BN hB.
have hRef:=@finite_continuous_dual_reflexive R [the finType of 'I_n] V D B e he N hN
  ed DN hD eb BN hB tau ht.
have hAE:=@reflexive_bv_derivative_ae R V D B N hN ed DN hD eb BN hB tau f hComplete ht hRef hBV.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hAE)=>x [v [hv _]].
by exists v.
Qed.
