(** Federer (1969), 4.1.5, p. 350:
    the actual abstract Y* can be used with
    the earlier partial-domain integration theorem
    of 2.5.12. The auxiliary weak-dual presentation
    preserves every evaluation and the original norm;
    its weak continuity preserves measurability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground ContinuousDualUP
  VectorDaniellHypotheses WeakDualFunctionalNorm RealFunctionalNormUP
  OpenFamilyTopologyMathcomp NormOpenTopology WeakEvaluationTopologyUP WeakEvaluationTopologyLaws
  ScalarNormExtendedEmbedding IsotropyGroupTopology DaniellSpaceWeakTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section AbstractDualWeakEncoding.
Variable R:realType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.

(** Source for [abstract_dual_functional_laws]: the original
    actual functional viewed in the earlier weak
    presentation, supporting the partial L1 extension
    in Federer 4.1.5, p. 350. *)
Lemma abstract_dual_functional_laws (d:D):dual_space hNY (fun y=>ed d y).
Proof.
split.
- move=>c u v; by rewrite linearD linearZ.
- exact:continuous_dual_continuous hD d.
Qed.

(** Source for [abstract_dual_weak_point]: exact evaluation
    in the earlier weak presentation, supporting the
    partial L1 extension in Federer 4.1.5, p. 350. *)
Definition abstract_dual_weak_point (d:D):weak_dual_space hNY:=
  @exist (weak_function_space Y) (fun alpha=>alpha \in (dual_space hNY:set (weak_function_space Y)))
    (fun y=>ed d y) (mem_set (abstract_dual_functional_laws d)).

(** Source for [abstract_dual_weak_point_evaluation]:
    the original dual evaluation is unchanged,
    Federer 4.1.5, p. 350. *)
Lemma abstract_dual_weak_point_evaluation d y:
  val (abstract_dual_weak_point d) y=ed d y.
Proof. reflexivity. Qed.

(** Source for [abstract_dual_weak_point_norm]: the
    original norm is unchanged by the auxiliary
    presentation, Federer 4.1.5, p. 350. *)
Theorem abstract_dual_weak_point_norm d:
  dual_norm NY (val (abstract_dual_weak_point d))=DN d.
Proof.
have hNorm:=@weak_dual_functional_norm_laws R Y NY hNY (abstract_dual_weak_point d).
have hHom:weak_dual_functional_hom (abstract_dual_weak_point d)=ed d.
  apply:hom_ext=>y; by rewrite /weak_dual_functional_hom /abstract_dual_weak_point /=.
rewrite hHom in hNorm.
exact:real_functional_norm_unique hNorm (continuous_dual_norm_laws hD d).
Qed.

(** Source for [abstract_dual_weak_point_continuous]:
    weak continuity of the exact auxiliary dual
    presentation used for the original partial L1
    extension, Federer 4.1.5, p. 350. *)
Theorem abstract_dual_weak_point_continuous (O:set (set D))
    (hO:is_weak_evaluation_topology (fun a y=>ed a y) O):
  continuous (fun d:open_family_topological_space hO.1=>abstract_dual_weak_point d).
Proof.
pose A:=open_family_topological_space hO.1.
apply:(@set_type_continuous_into (weak_function_space Y)
  (dual_space hNY:set (weak_function_space Y)) A (fun d:A=>abstract_dual_weak_point d)).
move=>d.
have hFilter:Filter ((fun a:A=>val (abstract_dual_weak_point a)) @ nbhs d):=
  fmap_filter _ (@nbhs_filter A d).
apply/(@product_topology_cvg Y (@weak_factor R Y) _ _ hFilter)=>y.
have hCoordinate:=@weak_evaluation_continuous R Y D (fun a y=>ed a y) O hO y.
have hNorm:continuous (fun a:A=>(ed a y:real_norm_metric_space (@scalar_absolute_value_norm R))).
  by rewrite continuousP.
exact:(@continuous_comp A (real_norm_metric_space (@scalar_absolute_value_norm R)) (real_line_metric R)
  (fun a:A=>ed a y) (fun z:real_norm_metric_space (@scalar_absolute_value_norm R)=>(z:real_line_metric R))
  d (hNorm d) (@scalar_norm_real_identity_continuous R (ed d y))).
Qed.
End AbstractDualWeakEncoding.
