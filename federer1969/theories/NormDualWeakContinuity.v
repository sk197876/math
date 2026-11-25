(** Federer (1969), 4.1.2, p. 347: norm
    continuity of the actual dual density implies its
    weak continuity. The independently specified weak topology
    is used through its universal mapping property. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormMetricScaleContinuity ContinuousDualUP ContinuousDualNorm RealFunctionalNormUP
  OpenFamilyTopologyUP NormOpenTopology WeakEvaluationTopologyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_dual_weak_continuous]: norm-to-weak continuity
    for the original Y* of Federer 4.1.2,
    p. 347. No separability or finite dimension
    of either Y or its dual is assumed. *)
Theorem norm_dual_weak_continuous (R:realType) (Y:lmodType R) (NY:Y->R)
    (hNY:is_real_norm NY) (YD:lmodType R) (ed:Hom YD (Hom Y R^o)) (DN:YD->R)
    (hYD:is_continuous_dual hNY ed DN) (O:set (set YD))
    (hO:is_weak_evaluation_topology (fun a y=>ed a y) O):
  open_family_continuous (norm_open_family (continuous_dual_norm_is_norm hYD)) O (fun a=>a).
Proof.
pose hDN:=continuous_dual_norm_is_norm hYD.
pose P:=norm_open_family hDN.
have hP:is_open_family_topology P:=(norm_open_family_seminorm_laws hDN).1.
apply:(hO.2 YD P hP (fun a=>a)).2=>y.
have hContinuous:continuous (fun a:real_norm_metric_space hDN=>
    (ed a y:real_norm_metric_space (@scalar_absolute_value_norm R))).
  apply:(@metric_fixed_lipschitz_continuous R (real_norm_metric_space hDN)
    (real_norm_metric_space (@scalar_absolute_value_norm R))
    (fun a=>ed a y) (NY y) (real_seminorm_nonnegative hNY.1 y))=>a b.
  have hEval:ed (a-b) y=ed a y-ed b y.
    exact:(congr1 (fun F:Hom Y R^o=>F y) (linearB (hom_as_linear ed) a b)).
  change (`|ed a y-ed b y|<=NY y*DN (a-b)).
  rewrite -hEval mulrC.
  exact:(real_functional_norm_bound (continuous_dual_norm_laws hYD (a-b)) y).
move:hContinuous; rewrite continuousP=>hContinuous A hA.
exact:hContinuous A hA.
Qed.
