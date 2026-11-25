(** Federer (1969), 4.1.4, p. 348: locality of the
    original derivative under extension by zero. The proof
    uses the already proved higher derivative and exact
    compact-support laws of the actual extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP SmoothTestSpaces
  SmoothTestEvaluation SmoothRestrictionUP SmoothRestrictionSealed SmoothRestrictionDerivatives TestZeroExtensionUP TestZeroExtensionLaws TestZeroExtensionDerivatives
  SmoothCompactSet SmoothCompactDomainInclusion SmoothFunctionSupport DistributionDirectionalDerivative TestDirectionalValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestZeroExtensionDirectional.
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
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variables DA:forall k,X->Hom A (Z k).
Variables DB:forall k,X->Hom B (Z k).
Hypothesis hDA:@is_smooth_function_derivatives R X Y NX NY hNX hNY U A evA DA.
Hypothesis hDB:@is_smooth_function_derivatives R X Y NX NY hNX hNY V B evB DB.
Local Notation TA := (smooth_test_space hA).
Local Notation TB := (smooth_test_space hB).
Local Notation incA := (smooth_test_inclusion hA).
Local Notation incB := (smooth_test_inclusion hB).
Variable L:Hom TA TB.
Hypothesis hL:is_test_zero_extension U V (smooth_test_value hA) (smooth_test_value hB) L.


Hypothesis hV:forall x,V x ->norm_domain_interior NX V x.
Variable v:X.
Local Notation DPA := (@distribution_test_directional_derivative R X Y NX NY hNX hNY U hU A evA hA DA hDA v).
Local Notation DPB := (@distribution_test_directional_derivative R X Y NX NY hNX hNY V hV B evB hB DB hDB v).

(** Source for [test_zero_extension_directional_commutes]: the
    original derivative of a zero-extended test equals the
    zero extension of its derivative, used in the initial
    localization of Federer 4.1.4, p. 348. Actual higher
    derivative agreement handles U; compact support handles
    every point outside U. *)
Theorem test_zero_extension_directional_commutes f:L (DPA f)=DPB (L f).
Proof.
have[K hK]:=smooth_test_support_bound hA f.
pose KV:=@smooth_compact_domain_inclusion R X NX hNX U V hUV K.
have hExtended:=@test_zero_extension_preserves_compact_bound R X Y NX NY hNX hNY
  U V hUV A B evA evB hA hB L hL K f hK.
have hDerivative:=@distribution_test_directional_derivative_compact_support R X Y NX NY hNX hNY
  V hV B evB hB DB hDB v KV (L f) hExtended.
apply:(smooth_test_values_extensional hB)=>x hxV.
rewrite (@test_zero_extension_value R X Y NX NY hNX hNY U V A B evA evB hA hB L hL (DPA f) x).
case:(pselect (U x))=>[hxU|hxU].
- rewrite (@distribution_test_directional_derivative_value R X Y NX NY hNX hNY
    U hU A evA hA DA hDA v f x hxU).
  rewrite (@distribution_test_directional_derivative_value R X Y NX NY hNX hNY
    V hV B evB hB DB hDB v (L f) x hxV).
  by rewrite (@test_zero_extension_higher_derivative R X Y NX NY hNX hNY U V hU hUV
    A B evA evB hA hB DA DB hDA hDB L hL 1%N f x hxU).
- rewrite (@smooth_test_value_outside R X Y NX NY hNX hNY U A evA hA (DPA f) x hxU).
  have hOutside:~smooth_compact_carrier KV x.
    move=>hx; exact:hxU (smooth_compact_in_domain K x hx).
  have hZero:evB (incB (DPB (L f))) x=0.
    exact:(smooth_function_compact_support_iff hB KV _).1 hDerivative x hOutside.
  exact:esym hZero.
Qed.
End TestZeroExtensionDirectional.
