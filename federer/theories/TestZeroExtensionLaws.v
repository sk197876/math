(** Federer (1969), 4.1.1, p. 345: zero extension
    preserves the exact test support and is injective.
    These laws follow from the public extension values
    and the actual compact-support test representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric SmoothCompactSet SmoothCompactDomainInclusion
  SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation TestZeroExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestZeroExtensionLaws.
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
Local Notation incA := (smooth_test_inclusion hA).
Local Notation incB := (smooth_test_inclusion hB).
Local Notation valueA := (smooth_test_value hA).
Local Notation valueB := (smooth_test_value hB).
Variable L:Hom TA TB.
Hypothesis hL:is_test_zero_extension U V valueA valueB L.

(** Source for [test_zero_extension_value]: normalized
    total representatives agree at every source point,
    supporting the exact zero extension in Federer
    4.1.1, p. 345. *)
Theorem test_zero_extension_value f x:valueB (L f) x=valueA f x.
Proof.
case:(pselect (U x))=>[hx|hx].
- exact:(@test_zero_extension_original R X Y TA TB U V valueA valueB L hL f x hx).
- rewrite (@smooth_test_value_outside R X Y NX NY hNX hNY U A evA hA f x hx).
  case:(pselect (V x))=>[hv|hv].
  + exact:(@test_zero_extension_zero R X Y TA TB U V valueA valueB L hL f x hv hx).
  + exact:(@smooth_test_value_outside R X Y NX NY hNX hNY V B evB hB (L f) x hv).
Qed.

(** Source for [test_zero_extension_preserves_compact_bound]:
    a test supported in K extends to a test supported
    in that same K, Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_preserves_compact_bound (K:smooth_compact_set hNX U) f:
  @smooth_function_support R X Y NX hNX U TA valueA f `<=` smooth_compact_carrier K ->
  @smooth_function_support R X Y NX hNX V TB valueB (L f) `<=` smooth_compact_carrier K.
Proof.
move=>hf.
pose KV:=@smooth_compact_domain_inclusion R X NX hNX U V hUV K.
change (@smooth_function_support R X Y NX hNX V B evB (incB (L f)) `<=` smooth_compact_carrier KV).
apply:(smooth_function_compact_support_iff hB KV (incB (L f))).2=>x hx.
change (valueB (L f) x=0); rewrite test_zero_extension_value.
exact:((smooth_function_compact_support_iff hA K (incA f)).1 hf x hx).
Qed.

(** Source for [test_zero_extension_support]: extension
    by zero preserves the actual support, supporting
    the monomorphism and fixed-K comparison in
    Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_support f:
  @smooth_function_support R X Y NX hNX V TB valueB (L f)=
  @smooth_function_support R X Y NX hNX U TA valueA f.
Proof.
have hValue:(valueB (L f))=valueA f by apply:funext=>x; exact:test_zero_extension_value.
have [K hK]:=smooth_test_support_bound hA f.
have hBound:=test_zero_extension_preserves_compact_bound hK.
apply:funext=>x; apply:propext; split.
- move=>hx; split.
  + exact:smooth_compact_in_domain K x (hBound x hx).
  + move:hx.2; by rewrite hValue.
- move=>[hx hCl]; split; first exact:(@hUV x hx).
  by rewrite hValue.
Qed.

(** Source for [test_zero_extension_injective]: actual
    zero extension is one-to-one, the monomorphism
    in Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_injective:injective L.
Proof.
move=>f g he; apply:(smooth_test_values_extensional hA)=>x hx.
by rewrite -(test_zero_extension_value f x) -(test_zero_extension_value g x) he.
Qed.
End TestZeroExtensionLaws.
