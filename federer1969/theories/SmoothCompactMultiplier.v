(** Federer (1969), 4.1.1, pp. 344–345: multiplication
    by a compactly supported smooth scalar maps E continuously
    into a single D_K and hence into the literal final
    test-function topology. All maps use opaque corestriction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP NormRegularity
  ContinuousMultilinearSealed CompactSupportFunctionUP OpenFamilyTopologyUP InitialOpenTopologyUP
  FinalOpenTopologyUP LinearSubspaceRepresentationUP LinearSubspaceLiftSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSubspaces
  SmoothTestSpaces SmoothTestTopology SmoothFunctionTopology SmoothMultiplierUP
  SmoothMultiplierSupport SmoothMultiplierContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section CompactMultiplier.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u.
Variable P:Hom E E.
Hypothesis hP:is_smooth_multiplier U ev u P.
Variable K:smooth_compact_set hNX U.
Hypothesis hK:@real_function_support R (real_norm_metric_space hNX) u `<=` smooth_compact_carrier K.
Local Notation DK := (smooth_fixed_test_space hE K).
Local Notation DT := (smooth_test_space hE).
Local Notation k := (smooth_fixed_test_inclusion hE K).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation j := (smooth_test_step hE K).
Local Notation EO := (smooth_function_opens hD).
Local Notation PK := (smooth_test_step_opens hE hD K).
Local Notation SO := (smooth_test_opens hE hD).

(** Source for [smooth_compact_multiplier_member]: every
    product lies in the prescribed D_K, supporting the
    compact-support extension of Federer 4.1.1, p. 345. *)
Lemma smooth_compact_multiplier_member f:
  smooth_fixed_support_subspace hE K (P f).
Proof.
exact (@smooth_multiplier_compact_scalar_support R X Y NX NY hNX hNY U E ev hE u P hP K hK f).
Qed.

(** Source for [smooth_compact_multiplier_fixed]: the actual
    map E to D_K given by u phi, supporting Federer
    4.1.1, pp. 344–345. *)
Definition smooth_compact_multiplier_fixed:Hom E DK:=
  @LinearSubspaceLift.map R E DK E (smooth_fixed_support_subspace hE K) k
    (smooth_fixed_test_space_laws hE K) P smooth_compact_multiplier_member.

(** Source for [smooth_compact_multiplier_fixed_evaluation]:
    the fixed-support product represents exactly u phi,
    supporting Federer 4.1.1, pp. 344–345. *)
Lemma smooth_compact_multiplier_fixed_evaluation f:
  k (smooth_compact_multiplier_fixed f)= P f.
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [smooth_compact_multiplier_fixed_continuous]:
    E to D_K is continuous for the original relative topology,
    supporting compact-support dual extension in Federer
    4.1.1, p. 345. *)
Theorem smooth_compact_multiplier_fixed_continuous:
  open_family_continuous EO PK smooth_compact_multiplier_fixed.
Proof.
have hRel:=@smooth_test_step_relative_topology R X Y NX NY hNX hNY U E ev hE D hD K.
apply:(@initial_open_topology_mapping DK E E EO k PK EO smooth_compact_multiplier_fixed hRel).2.
have he:(fun f:E=>k (smooth_compact_multiplier_fixed f))= P.
  apply:funext=>f; exact:smooth_compact_multiplier_fixed_evaluation.
rewrite he.
exact (@smooth_multiplier_continuous R X Y NX NY hNX hNY U hU E ev hE D hD u hu P hP).
Qed.

(** Source for [smooth_compact_multiplier_test]: the actual
    E to D map given by compactly supported multiplication,
    supporting Federer 4.1.1, p. 345. *)
Definition smooth_compact_multiplier_test:Hom E DT:=hom_comp j smooth_compact_multiplier_fixed.

(** Source for [smooth_compact_multiplier_test_evaluation]:
    inclusion of this test product in E recovers u phi,
    supporting Federer 4.1.1, p. 345. *)
Lemma smooth_compact_multiplier_test_evaluation f:
  inc (smooth_compact_multiplier_test f)= P f.
Proof. by rewrite /smooth_compact_multiplier_test hom_compE smooth_test_step_evaluation smooth_compact_multiplier_fixed_evaluation. Qed.

(** Source for [smooth_compact_multiplier_test_continuous]:
    E to D is continuous even for Federer's literal final
    topology, supporting the compact-support dual extension
    in Federer 4.1.1, p. 345. *)
Theorem smooth_compact_multiplier_test_continuous:
  open_family_continuous EO SO smooth_compact_multiplier_test.
Proof.
exact (@open_family_continuous_compose E DK DT EO PK SO smooth_compact_multiplier_fixed j
  smooth_compact_multiplier_fixed_continuous
  (@final_open_topology_inclusion (smooth_compact_set hNX U)
    (fun L=>smooth_fixed_test_space hE L) DT (smooth_test_step_opens hE hD)
    (fun L f=>smooth_test_step hE L f) SO (smooth_test_final_topology_laws hE hD) K)).
Qed.
End CompactMultiplier.
