(** Federer (1969), 4.1.1, p. 346: the
    original weak dual field gives an opaque
    distribution. The integral action was specified
    independently; existence and continuity were
    proved before selecting this witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP ContinuousMultilinearSealed ContinuousDualUP
  VectorDaniellHypotheses OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP MeasureUP
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  ContinuousRealDual DistributionIntegralFieldUP DistributionIntegralFunctionalContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type DistributionFromDualFieldSignature.
(** Source for [value]: the distribution corresponding
    to a weak field with locally integrable
    dual norm, Federer 4.1.1, p. 346. *)
Parameter value:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (YD:lmodType R) (ed:Hom YD (Hom Y R^o)) (DN:YD->R)
    (hYD:is_continuous_dual hNY ed DN) (hSep:is_separable_normed_space hNY)
    (O:set (set YD)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu)
    (hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A)
    (xi:X->YD) (hField:@is_locally_integrable_weak_dual_field R X Y NX hNX YD ed DN O hO mu xi)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY (fun _=>True) ev)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D),
  @continuous_real_dual_space R (smooth_test_space hE) (smooth_test_opens hE hD)
      (smooth_test_final_topology_laws hE hD).1.
(** Source for [laws]: every test evaluation is
    exactly the original pairing integral,
    Federer 4.1.1, p. 346. *)
Parameter laws:forall (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (YD:lmodType R) (ed:Hom YD (Hom Y R^o)) (DN:YD->R)
    (hYD:is_continuous_dual hNY ed DN) (hSep:is_separable_normed_space hNY)
    (O:set (set YD)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu)
    (hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A)
    (xi:X->YD) (hField:@is_locally_integrable_weak_dual_field R X Y NX hNX YD ed DN O hO mu xi)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY (fun _=>True) ev)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D),
  is_distribution_integral_action mu ed xi (smooth_test_value hE)
    (@continuous_real_dual_evaluation R (smooth_test_space hE) (smooth_test_opens hE hD)
      (smooth_test_final_topology_laws hE hD).1 (@value R X Y NX NY hNX hNY YD ed DN hYD hSep O hO mu hm hOpen xi hField E ev hE D hD)).
End DistributionFromDualFieldSignature.
Module DistributionFromDualField:DistributionFromDualFieldSignature.
(** Source for [value]: hide the already proved
    distribution witness for Federer 4.1.1,
    p. 346. *)
Definition value (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (YD:lmodType R) (ed:Hom YD (Hom Y R^o)) (DN:YD->R)
    (hYD:is_continuous_dual hNY ed DN) (hSep:is_separable_normed_space hNY)
    (O:set (set YD)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu)
    (hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A)
    (xi:X->YD) (hField:@is_locally_integrable_weak_dual_field R X Y NX hNX YD ed DN O hO mu xi)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY (fun _=>True) ev)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D):
  @continuous_real_dual_space R (smooth_test_space hE) (smooth_test_opens hE hD)
      (smooth_test_final_topology_laws hE hD).1:=
  projT1 (cid (@distribution_from_dual_field_exists R X Y NX NY hNX hNY YD ed DN hYD hSep O hO mu hm hOpen xi
    (@integrable_dual_field_weak_measurable R X Y NX hNX YD ed DN O hO mu xi hField)
    E ev hE D hD (@integrable_dual_field_local_norm R X Y NX hNX YD ed DN O hO mu xi hField))).
(** Source for [laws]: the hidden distribution
    has exactly the independently specified
    integral action, Federer 4.1.1, p. 346. *)
Lemma laws (R:realType) (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (YD:lmodType R) (ed:Hom YD (Hom Y R^o)) (DN:YD->R)
    (hYD:is_continuous_dual hNY ed DN) (hSep:is_separable_normed_space hNY)
    (O:set (set YD)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O)
    (mu:set X->\bar R) (hm:is_measure mu)
    (hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A)
    (xi:X->YD) (hField:@is_locally_integrable_weak_dual_field R X Y NX hNX YD ed DN O hO mu xi)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY (fun _=>True) ev)
    (D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D):
  is_distribution_integral_action mu ed xi (smooth_test_value hE)
    (@continuous_real_dual_evaluation R (smooth_test_space hE) (smooth_test_opens hE hD)
      (smooth_test_final_topology_laws hE hD).1 (@value R X Y NX NY hNX hNY YD ed DN hYD hSep O hO mu hm hOpen xi hField E ev hE D hD)).
Proof. exact:(projT2 (cid (@distribution_from_dual_field_exists R X Y NX NY hNX hNY YD ed DN hYD hSep O hO mu hm hOpen xi
    (@integrable_dual_field_weak_measurable R X Y NX hNX YD ed DN O hO mu xi hField)
    E ev hE D hD (@integrable_dual_field_local_norm R X Y NX hNX YD ed DN O hO mu xi hField)))). Qed.
End DistributionFromDualField.
