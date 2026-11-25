(** Federer (1969), 4.1.1, p. 345: restriction
    is the actual inverse to fixed-support zero
    extension. The maps keep K unchanged and use
    the sealed smooth restriction and subspace lifts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP SmoothCompactSet SmoothCompactDomainInclusion
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSupport SmoothTestSubspaces SmoothTestSpaces
  SmoothTestEvaluation SmoothRestrictionUP SmoothRestrictionSealed TestZeroExtensionUP TestZeroExtensionLaws
  TestZeroExtensionFixed LinearSubspaceRepresentationUP LinearSubspaceLiftSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FixedTestExtensionInverse.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
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
Local Notation incA := (smooth_test_inclusion hA).
Local Notation incB := (smooth_test_inclusion hB).
Local Notation Q := (@SmoothRestriction.operator R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB).
Local Notation hQ := (@SmoothRestriction.laws R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB).
Local Notation F := (@test_zero_extension_fixed R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K).

(** Source for [test_fixed_restriction_member]: restricting
    a test supported in K remains supported in K,
    supporting the inverse map of Federer 4.1.1,
    p. 345. *)
Lemma test_fixed_restriction_member (g:BK):
  smooth_fixed_support_subspace hA K (hom_comp Q kB g).
Proof.
apply:(smooth_function_compact_support_iff hA K (Q (kB g))).2=>x hx.
case:(pselect (U x))=>[hu|hu].
- rewrite (@hQ (kB g) x hu).
  exact:((smooth_function_compact_support_iff hB KV (kB g)).1
    (subspace_representation_member (smooth_fixed_test_space_laws hB KV) g) x hx).
- exact:(@smooth_function_evaluation_outside R X Y NX NY hNX hNY U A evA hA (Q (kB g)) x hu).
Qed.

(** Source for [test_zero_extension_fixed_inverse]: the
    actual inverse fixed-support restriction, supporting
    the homeomorphism in Federer 4.1.1, p. 345. *)
Definition test_zero_extension_fixed_inverse:Hom BK AK:=
  @LinearSubspaceLift.map R BK AK A (smooth_fixed_support_subspace hA K) kA
    (smooth_fixed_test_space_laws hA K) (hom_comp Q kB) test_fixed_restriction_member.

(** Source for [test_zero_extension_fixed_inverse_evaluation]:
    the inverse represents the original smooth restriction,
    supporting Federer 4.1.1, p. 345. *)
Lemma test_zero_extension_fixed_inverse_evaluation g:
  kA (test_zero_extension_fixed_inverse g)=Q (kB g).
Proof. exact:LinearSubspaceLift.evaluation. Qed.

(** Source for [test_zero_extension_fixed_left_inverse]:
    restricting a fixed-support extension recovers the
    original test, Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_fixed_left_inverse:cancel F test_zero_extension_fixed_inverse.
Proof.
move=>f; apply:(subspace_representation_injective (smooth_fixed_test_space_laws hA K)).
rewrite test_zero_extension_fixed_inverse_evaluation test_zero_extension_fixed_evaluation.
apply:(smooth_function_extensional hA)=>x hx.
rewrite (@hQ (incB (L (jA f))) x hx).
have he:=@test_zero_extension_original R X Y TA TB U V (smooth_test_value hA) (smooth_test_value hB)
  L hL (jA f) x hx.
change (evB (incB (L (jA f))) x=evA (incA (jA f)) x) in he.
by rewrite smooth_test_step_evaluation in he.
Qed.

(** Source for [test_zero_extension_fixed_right_inverse]:
    every test in D_K(V,Y) is the extension of
    its restriction to U, Federer 4.1.1,
    p. 345. *)
Theorem test_zero_extension_fixed_right_inverse:cancel test_zero_extension_fixed_inverse F.
Proof.
move=>g; apply:(subspace_representation_injective (smooth_fixed_test_space_laws hB KV)).
rewrite test_zero_extension_fixed_evaluation.
apply:(smooth_function_extensional hB)=>x hx.
change (smooth_test_value hB (L (jA (test_zero_extension_fixed_inverse g))) x=evB (kB g) x).
rewrite (@test_zero_extension_value R X Y NX NY hNX hNY U V A B evA evB hA hB L hL
  (jA (test_zero_extension_fixed_inverse g)) x).
rewrite /smooth_test_value smooth_test_step_evaluation test_zero_extension_fixed_inverse_evaluation.
case:(pselect (U x))=>[hu|hu]; first exact:(@hQ (kB g) x hu).
rewrite (@smooth_function_evaluation_outside R X Y NX NY hNX hNY U A evA hA (Q (kB g)) x hu).
symmetry; apply:((smooth_function_compact_support_iff hB KV (kB g)).1
  (subspace_representation_member (smooth_fixed_test_space_laws hB KV) g) x)=>hKx.
exact:hu (smooth_compact_in_domain K x hKx).
Qed.
End FixedTestExtensionInverse.
