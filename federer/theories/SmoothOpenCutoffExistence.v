(** Federer (1969), 4.1.8, p. 360: apply
    4.1.3 on the whole Euclidean space and localise back
    to the original open set. This supporting operator uses
    the actual smooth restriction and compact multiplier
    already proved for 4.1.1, pp. 344–345. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  ContinuousMultilinearSealed NormMetric SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces
  SmoothTestEvaluation SmoothTestTopology SmoothFunctionTopology CompactSupportFunctionUP
  OpenFamilyTopologyUP SmoothRestrictionSealed SmoothRestrictionContinuity
  SmoothMultiplierSealed SmoothCompactMultiplier.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothOpenCutoffExistence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Y).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNY (fun _=>True) fv.
Variable DE:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable DF:forall k,X->Hom F (@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Hypothesis hDE:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev DE.
Hypothesis hDF:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) F fv DF.
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u.
Variable K:smooth_compact_set hNX U.
Hypothesis hK:@real_function_support R (NormMetric.real_norm_metric_space hNX) u
  `<=` smooth_compact_carrier K.

(** Source for [smooth_open_cutoff_exists]: restriction
    followed by the given compact smooth scalar multiplier
    maps E(R^n,Y) continuously into the original D(U,Y),
    supporting Federer 4.1.8, p. 360. Its exact
    pointwise formula precedes any choice of operator. *)
Theorem smooth_open_cutoff_exists:
  exists L:Hom F (smooth_test_space hE),
    (forall f x,U x->smooth_test_value hE (L f) x=u x*:fv f x) /\
    open_family_continuous (smooth_function_opens hDF) (smooth_test_opens hE hDE) L.
Proof.
pose hLocal:=hu.
pose restriction:=@SmoothRestriction.operator R X Y NX NY hNX hNY U (fun _=>True)
  hU (fun _ _=>I) E F ev fv hE hF.
have hRestriction:=@SmoothRestriction.laws R X Y NX NY hNX hNY U (fun _=>True)
  hU (fun _ _=>I) E F ev fv hE hF.
pose multiplier:=@SmoothMultiplier.operator R X Y NX NY hNX hNY U E ev hE u hLocal.
have hMultiplier:=@SmoothMultiplier.laws R X Y NX NY hNX hNY U E ev hE u hLocal.
pose cutoff:=@smooth_compact_multiplier_test R X Y NX NY hNX hNY U E ev hE
  u multiplier hMultiplier K hK.
exists (hom_comp cutoff restriction);split.
- move=>f x hx.
  change (ev (smooth_test_inclusion hE (cutoff (restriction f))) x=u x*:fv f x).
  rewrite (@smooth_compact_multiplier_test_evaluation R X Y NX NY hNX hNY U E ev hE
    u multiplier hMultiplier K hK (restriction f)) (hMultiplier _ x hx) (hRestriction _ x hx).
  reflexivity.
- exact:(open_family_continuous_compose
    (@smooth_restriction_continuous R X Y NX NY hNX hNY U (fun _=>True) hU (fun _ _=>I)
      E F ev fv DE DF hDE hDF restriction hRestriction)
    (@smooth_compact_multiplier_test_continuous R X Y NX NY hNX hNY U hU E ev hE
      DE hDE u hLocal multiplier hMultiplier K hK)).
Qed.
End SmoothOpenCutoffExistence.
