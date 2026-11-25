(** Federer (1969), 4.1.1, p. 345: zero extension
    preserves all original higher derivatives on U.
    The proof reuses the actual smooth restriction
    operator and its already proved derivative law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP SmoothTestSpaces
  SmoothTestEvaluation SmoothRestrictionUP SmoothRestrictionSealed SmoothRestrictionDerivatives TestZeroExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section TestZeroExtensionDerivatives.
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

(** Source for [test_zero_extension_higher_derivative]: the
    actual higher differentials agree on the original
    domain, supporting the continuous fixed-K extension
    in Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_higher_derivative j f x:U x ->
  DA j x (incA f)=DB j x (incB (L f)).
Proof.
move=>hx.
pose Q:=@SmoothRestriction.operator R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB.
have hQ:=@SmoothRestriction.laws R X Y NX NY hNX hNY U V hU hUV A B evA evB hA hB.
have hBack:Q (incB (L f))=incA f.
  apply:(smooth_function_extensional hA)=>y hy.
  rewrite (@hQ (incB (L f)) y hy).
  exact:(@test_zero_extension_original R X Y TA TB U V (smooth_test_value hA) (smooth_test_value hB)
    L hL f y hy).
have hSame:=@smooth_restriction_higher_derivative R X Y NX NY hNX hNY U V hU hUV A B evA evB
  DA DB hDA hDB Q hQ j (incB (L f)) x hx.
by rewrite hBack in hSame.
Qed.
End TestZeroExtensionDerivatives.
