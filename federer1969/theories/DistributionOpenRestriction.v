(** Federer (1969), 4.1.1, p. 345: extension
    by zero induces the continuous dual restriction
    D'(V,Y) to D'(U,Y). Its image contains
    every distribution with compact support in U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  OpenFamilyTopologyUP LinearSubspaceRepresentationUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology FunctionalSupportUP
  SmoothRestrictionUP SmoothRestrictionSealed SmoothRestrictionContinuity SmoothRestrictionTestExtension
  TestZeroExtensionUP TestZeroExtensionSealed TestZeroExtensionContinuity
  ContinuousRealDual ContinuousRealDualTranspose SmoothDualRestriction SmoothDualCompactImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionOpenRestriction.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Hypothesis hV:forall x,V x ->norm_domain_interior NX V x.
Hypothesis hUV:forall x,U x ->V x.
Variables A B:lmodType R.
Variable evA:A->X->Y.
Variable evB:B->X->Y.
Hypothesis hA:is_smooth_function_space hNX hNY U evA.
Hypothesis hB:is_smooth_function_space hNX hNY V evB.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variables DA:forall k,X->Hom A (Z k).
Variables DB:forall k,X->Hom B (Z k).
Hypothesis hDA:@is_smooth_function_derivatives R X Y NX NY hNX hNY U A evA DA.
Hypothesis hDB:@is_smooth_function_derivatives R X Y NX NY hNX hNY V B evB DB.
Local Notation TA := (smooth_test_space hA).
Local Notation TB := (smooth_test_space hB).
Local Notation SA := (smooth_test_opens hA hDA).
Local Notation SB := (smooth_test_opens hB hDB).
Local Notation hSA := (smooth_test_final_topology_laws hA hDA).1.
Local Notation hSB := (smooth_test_final_topology_laws hB hDB).1.
Local Notation DDA := (@continuous_real_dual_space R TA SA hSA).
Local Notation DDB := (@continuous_real_dual_space R TB SB hSB).
Local Notation eA := (@continuous_real_dual_evaluation R TA SA hSA).
Local Notation eB := (@continuous_real_dual_evaluation R TB SB hSB).
Local Notation DOA := (@continuous_real_dual_weak_opens R TA SA hSA).
Local Notation DOB := (@continuous_real_dual_weak_opens R TB SB hSB).
Local Notation L := (@TestZeroExtension.operator R X Y NX NY hNX hNY U V hV hUV A B evA evB hA hB).
Local Notation hL := (@TestZeroExtension.laws R X Y NX NY hNX hNY U V hV hUV A B evA evB hA hB).
Local Notation hLC := (@test_zero_extension_continuous R X Y NX NY hNX hNY U V hU hV hUV A B evA evB hA hB
  DA DB hDA hDB L hL).

(** Source for [distribution_open_restriction]: the actual
    dual linear map induced by test zero extension,
    Federer 4.1.1, p. 345. *)
Definition distribution_open_restriction:Hom DDB DDA:=
  @continuous_real_dual_transpose R TA TB SA SB hSA hSB L hLC.

(** Source for [distribution_open_restriction_evaluation]:
    restriction evaluates the original distribution on
    the zero-extended test, supporting the dual map
    in Federer 4.1.1, p. 345. *)
Theorem distribution_open_restriction_evaluation T f:
  eA (distribution_open_restriction T) f=eB T (L f).
Proof. exact:continuous_real_dual_transpose_evaluation. Qed.

(** Source for [distribution_open_restriction_continuous]:
    the actual dual open-set restriction is continuous
    in the original weak topologies, Federer
    4.1.1, p. 345. *)
Theorem distribution_open_restriction_continuous:
  open_family_continuous DOB DOA distribution_open_restriction.
Proof. exact:continuous_real_dual_transpose_weak_continuous. Qed.

Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.

(** Source for [distribution_open_restriction_compact_image]:
    every distribution with compact support in U
    is in the image of D'(V,Y) to D'(U,Y),
    Federer 4.1.1, p. 345. The proof reuses
    the proved E' image and the smooth restriction. *)
Theorem distribution_open_restriction_compact_image (S:DDA):
  compact [set x:real_norm_metric_space hNX|
    @smooth_functional_support R X Y NX hNX U TA (smooth_test_value hA) (eA S) x] ->
  exists T:DDB,distribution_open_restriction T=S.
Proof.
move=>hCompact.
pose OA:=smooth_function_opens hDA.
pose OB:=smooth_function_opens hDB.
pose hOA:=(smooth_function_topology_laws hDA).1.
pose hOB:=(smooth_function_topology_laws hDB).1.
pose EA:=@continuous_real_dual_space R A OA hOA.
pose EB:=@continuous_real_dual_space R B OB hOB.
pose ea:=@continuous_real_dual_evaluation R A OA hOA.
pose eb:=@continuous_real_dual_evaluation R B OB hOB.
pose rhoA:=@smooth_dual_test_restriction R X Y NX NY hNX hNY U A evA hA DA hDA.
pose rhoB:=@smooth_dual_test_restriction R X Y NX NY hNX hNY V B evB hB DB hDB.
have [T hT]:=(@smooth_dual_restriction_image R X Y NX NY hNX hNY n b hb U hU A evA hA DA hDA S).2 hCompact.
pose Q:=@SmoothRestriction.operator R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB.
pose hQ:=@SmoothRestriction.laws R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB.
pose hQC:=@smooth_restriction_continuous R X Y NX NY hNX hNY U V hU hUV A B evA evB DA DB hDA hDB Q hQ.
pose T0:EB:=@continuous_real_dual_transpose R B A OB OA hOB hOA Q hQC T.
exists (rhoB T0).
apply:(subspace_representation_injective (@continuous_real_dual_model_laws R TA SA hSA)).
apply:hom_ext=>f.
rewrite distribution_open_restriction_evaluation.
have hRhoB:=@smooth_dual_test_restriction_evaluation R X Y NX NY hNX hNY V B evB hB DB hDB T0 (L f).
rewrite hRhoB.
have hTrans:=@continuous_real_dual_transpose_evaluation R B A OB OA hOB hOA Q hQC T (smooth_test_inclusion hB (L f)).
rewrite hTrans (@smooth_restriction_test_extension_inverse R X Y NX NY hNX hNY U V A B evA evB hA hB Q L hQ hL f).
have hRhoA:=@smooth_dual_test_restriction_evaluation R X Y NX NY hNX hNY U A evA hA DA hDA T f.
rewrite -hRhoA.
exact:(congr1 (fun P:DDA=>eA P f) hT).
Qed.
End DistributionOpenRestriction.
