(** Federer (1969), 4.1.5, p. 349: the
    norm-preserving dual identification is continuous
    for the original weak topologies. Its exact
    evaluation law and the weak topology universal
    property prove continuity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground VectorDaniellHypotheses WeakDualRealisationUP
  OpenFamilyTopologyUP OpenFamilyTopologyMathcomp NormOpenTopology WeakEvaluationTopologyUP
  ScalarApproximateTargetTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [weak_dual_realisation_continuous]: weak
    measurability can be transported to the actual
    abstract Y* in Federer 4.1.5, p. 349,
    because the exact dual identification is weakly
    continuous. No norm-to-weak converse is assumed. *)
Theorem weak_dual_realisation_continuous (R:realType) (Y:lmodType R) (NY:Y->R)
    (hNY:is_real_norm NY) (D:lmodType R) (ed:Hom D (Hom Y R^o)) (DN:D->R)
    (J:weak_dual_space hNY->D) (hJ:is_weak_dual_realisation ed DN J)
    (O:set (set D)) (hO:is_weak_evaluation_topology (fun a y=>ed a y) O):
  continuous (fun a:weak_dual_space hNY=>(J a:open_family_topological_space hO.1)).
Proof.
pose A:=weak_dual_space hNY.
have hSource:is_open_family_topology (@open A).
  constructor.
  - exact:openT.
  - move=>B C; exact:openI.
  - move=>I B hB; apply:bigcup_open=>i _; exact:hB.
have hMap:open_family_continuous (@open A) O J.
  apply:(hO.2 A (@open A) hSource J).2=>y.
  have hEval:continuous (fun a:A=>(ed (J a) y:real_norm_metric_space (@scalar_absolute_value_norm R))).
    have hEq:(fun a:A=>ed (J a) y)=(fun a:A=>val a y).
      apply:funext=>a; exact:(@weak_dual_realisation_evaluation R Y NY hNY D ed DN J hJ a y).
    rewrite hEq.
    have hReal:continuous (fun a:A=>(val a y:real_line_metric R)):=
      @weak_dual_evaluation_continuous R Y NY hNY y.
    move=>a.
    exact:(@continuous_comp A (real_line_metric R)
      (real_norm_metric_space (@scalar_absolute_value_norm R))
      (fun b:A=>val b y) (fun z:real_line_metric R=>(z:real_norm_metric_space (@scalar_absolute_value_norm R)))
      a (hReal a) (@real_scalar_norm_identity_continuous R (val a y))).
  move:hEval; rewrite continuousP; by [].
move:hMap; rewrite continuousP; by [].
Qed.
