(** Federer (1969), 4.1.1, p. 345: the actual
    zero-extension map restricts to the fixed-support
    spaces indexed by the same compact K. The
    corestriction uses only the opaque subspace interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP SmoothCompactSet SmoothCompactDomainInclusion
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation
  LinearSubspaceRepresentationUP LinearSubspaceLiftSealed TestZeroExtensionUP TestZeroExtensionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FixedTestExtension.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:X->Prop.
Hypothesis hUV:forall x,U x ->V x.
Variables A B:lmodType R.
Variable evA:A->X->Y.
Variable evB:B->X->Y.
Hypothesis hA:is_smooth_function_space hNX hNY U evA.
Hypothesis hB:is_smooth_function_space hNX hNY V evB.
Local Notation TA := (smooth_test_space hA).
Local Notation TB := (smooth_test_space hB).
Variable L:Hom TA TB.
Hypothesis hL:is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB) L.
Variable K:smooth_compact_set hNX U.
Local Notation KV := (@smooth_compact_domain_inclusion R X NX hNX U V hUV K).
Local Notation AK := (smooth_fixed_test_space hA K).
Local Notation BK := (smooth_fixed_test_space hB KV).
Local Notation kA := (smooth_fixed_test_inclusion hA K).
Local Notation kB := (smooth_fixed_test_inclusion hB KV).
Local Notation jA := (smooth_test_step hA K).
Local Notation jB := (smooth_test_step hB KV).
Local Notation incA := (smooth_test_inclusion hA).
Local Notation incB := (smooth_test_inclusion hB).

(** Source for [test_zero_extension_fixed_member]: the
    extended original fixed-support test remains supported
    in K, supporting the D_K comparison in
    Federer 4.1.1, p. 345. *)
Lemma test_zero_extension_fixed_member (f:AK):
  smooth_fixed_support_subspace hB KV (hom_comp incB (hom_comp L jA) f).
Proof.
change (@smooth_function_support R X Y NX hNX V TB (smooth_test_value hB) (L (jA f)) `<=`
  smooth_compact_carrier K).
apply:(@test_zero_extension_preserves_compact_bound R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K (jA f)).
change (@smooth_function_support R X Y NX hNX U A evA (incA (jA f)) `<=` smooth_compact_carrier K).
rewrite smooth_test_step_evaluation.
exact:(subspace_representation_member (smooth_fixed_test_space_laws hA K) f).
Qed.

(** Source for [test_zero_extension_fixed]: the actual
    linear map D_K(U,Y) to D_K(V,Y),
    Federer 4.1.1, p. 345. *)
Definition test_zero_extension_fixed:Hom AK BK:=
  @LinearSubspaceLift.map R AK BK B (smooth_fixed_support_subspace hB KV) kB
    (smooth_fixed_test_space_laws hB KV) (hom_comp incB (hom_comp L jA)) test_zero_extension_fixed_member.

(** Source for [test_zero_extension_fixed_evaluation]: fixed-
    support extension agrees with actual test extension,
    supporting Federer 4.1.1, p. 345. *)
Lemma test_zero_extension_fixed_evaluation f:
  kB (test_zero_extension_fixed f)=incB (L (jA f)).
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [test_zero_extension_fixed_step_commutes]:
    including the fixed-support extension in D equals
    extending the included original test, supporting
    Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_fixed_step_commutes f:
  jB (test_zero_extension_fixed f)=L (jA f).
Proof.
apply:(subspace_representation_injective (smooth_test_space_laws hB)).
by rewrite smooth_test_step_evaluation test_zero_extension_fixed_evaluation.
Qed.
End FixedTestExtension.
