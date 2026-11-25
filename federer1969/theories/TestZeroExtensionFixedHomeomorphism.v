(** Federer (1969), 4.1.1, p. 345: zero
    extension maps D_K(U,Y) homeomorphically onto
    D_K(V,Y). Both inverse identities and the two
    original relative-topology continuities are proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP InitialOpenTopologyUP SmoothCompactSet SmoothCompactDomainInclusion
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothRestrictionUP SmoothRestrictionSealed SmoothRestrictionContinuity TestZeroExtensionUP TestZeroExtensionFixed
  TestZeroExtensionContinuity TestZeroExtensionFixedInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section FixedTestHomeomorphism.
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
Variable L:Hom TA TB.
Hypothesis hL:is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB) L.
Variable K:smooth_compact_set hNX U.
Local Notation KV := (@smooth_compact_domain_inclusion R X NX hNX U V hUV K).
Local Notation AK := (smooth_fixed_test_space hA K).
Local Notation BK := (smooth_fixed_test_space hB KV).
Local Notation kA := (smooth_fixed_test_inclusion hA K).
Local Notation kB := (smooth_fixed_test_inclusion hB KV).
Local Notation PA := (smooth_test_step_opens hA hDA K).
Local Notation PB := (smooth_test_step_opens hB hDB KV).
Local Notation F := (@test_zero_extension_fixed R X Y NX NY hNX hNY U V hUV A B evA evB hA hB L hL K).
Local Notation G := (@test_zero_extension_fixed_inverse R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB K).
Local Notation Q := (@SmoothRestriction.operator R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB).
Local Notation hQ := (@SmoothRestriction.laws R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB).

(** Source for [test_zero_extension_fixed_inverse_continuous]:
    the actual inverse restriction is continuous for
    the E-relative D_K topologies, supporting
    Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_fixed_inverse_continuous:open_family_continuous PB PA G.
Proof.
have hRelA:=@smooth_test_step_relative_topology R X Y NX NY hNX hNY U A evA hA DA hDA K.
have hRelB:=@smooth_test_step_relative_topology R X Y NX NY hNX hNY V B evB hB DB hDB KV.
apply:(@initial_open_topology_mapping AK A BK (smooth_function_opens hDA) kA PA PB G hRelA).2.
have he:(fun g:BK=>kA (G g))=(fun g=>Q (kB g)).
  apply:funext=>g; exact:test_zero_extension_fixed_inverse_evaluation.
rewrite he.
exact:(@open_family_continuous_compose BK B A PB (smooth_function_opens hDB) (smooth_function_opens hDA)
  kB Q (initial_open_topology_inclusion hRelB)
  (@smooth_restriction_continuous R X Y NX NY hNX hNY U V hU hUV A B evA evB DA DB hDA hDB Q hQ)).
Qed.

(** Source for [test_zero_extension_fixed_homeomorphism]:
    the original fixed-K zero-extension map has an
    actual continuous inverse and both cancellation
    laws, the homeomorphism asserted in Federer
    4.1.1, p. 345. *)
Theorem test_zero_extension_fixed_homeomorphism:
  cancel F G /\ cancel G F /\ open_family_continuous PA PB F /\ open_family_continuous PB PA G.
Proof.
split.
- exact:(@test_zero_extension_fixed_left_inverse R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB L hL K).
- split.
  + exact:(@test_zero_extension_fixed_right_inverse R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB L hL K).
  + split; last exact:test_zero_extension_fixed_inverse_continuous.
    exact:(@test_zero_extension_fixed_continuous R X Y NX NY hNX hNY U V hU hV hUV A B evA evB hA hB
      DA DB hDA hDB L hL K).
Qed.
End FixedTestHomeomorphism.
