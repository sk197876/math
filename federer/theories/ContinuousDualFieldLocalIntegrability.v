(** Federer (1969), 4.1.2, p. 347: the actual
    continuous dual-valued density satisfies the original weak
    measurability and local dual-norm integrability conditions
    of the distribution integral in 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormClassOneUP NormClassZeroTopology ContinuousDualUP ContinuousDualNorm
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  OpenFamilyTopologyUP OpenFamilyTopologyMathcomp NormOpenTopology WeakEvaluationTopologyUP NormDualWeakContinuity
  PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages MeasureUP MeasureAlmostBasic MeasurableFunctionUP
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext LocallyIntegrableVectorFieldUP
  ContinuousFieldLocalIntegrability DistributionIntegralFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_dual_field_locally_integrable]: the
    actual g_epsilon defines a distribution integral,
    Federer 4.1.2, p. 347, by the
    original sufficient condition of 4.1.1, p. 346. *)
Theorem continuous_dual_field_locally_integrable (R:realType) n (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (YD:lmodType R)
    (ed:Hom YD (Hom Y R^o)) (DN:YD->R) (hYD:is_continuous_dual hNY ed DN)
    (O:set (set YD)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (xi:R_n R n->YD):
  norm_class_zero (inner_norm (@euclidean_inner_productP R n)) DN (fun _=>True) xi ->
  @is_locally_integrable_weak_dual_field R (R_n R n) Y
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) YD ed DN O hO
    (@euclidean_lebesgue_measure R n) xi.
Proof.
move=>hf.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hDN:=continuous_dual_norm_is_norm hYD.
have hCont:continuous (fun x:real_norm_metric_space hN=>(xi x:real_norm_metric_space hDN)).
  move=>x; exact:(@norm_class_zero_continuous_at R X YD N DN hN hDN (fun _=>True) xi x hf Logic.I).
have hWeak:=@norm_dual_weak_continuous R Y NY hNY YD ed DN hYD O hO.
constructor.
- constructor.
  + rewrite partial_function_total_domain; exact:measure_almost_everywhere_true (euclidean_lebesgue_is_measure R n).
  + move=>A hA; rewrite partial_function_total_preimage.
    apply:(@euclidean_distribution_measure_open R n).
    have hAO:O A:=hA.
    have hPre:=@hWeak A hAO.
    move:hCont; rewrite continuousP=>hCont.
    exact:hCont A hPre.
- have hLocal:=@continuous_field_locally_norm_integrable R n YD DN hDN xi hf.
  exact:(@locally_integrable_vector_compact_norm R X YD N DN hN hDN
    (@euclidean_lebesgue_measure R n) xi hLocal).
Qed.
