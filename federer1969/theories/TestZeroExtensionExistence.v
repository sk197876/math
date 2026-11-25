(** Federer (1969), 4.1.1, p. 345: actual test
    zero extension exists and is linear. Compact support
    makes the normalized original function globally smooth,
    by the already proved local smooth gluing theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  SmoothCompactSet SmoothCompactDomainInclusion SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothCompactZeroExtension SmoothTestSpaces SmoothTestEvaluation SmoothTestRepresentation TestZeroExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TestZeroExtensionExistence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variables U V:X->Prop.
Hypothesis hV:forall x,V x ->norm_domain_interior NX V x.
Hypothesis hUV:forall x,U x ->V x.
Variables A B:lmodType R.
Variable evA:A->X->Y.
Variable evB:B->X->Y.
Hypothesis hA:is_smooth_function_space hNX hNY U evA.
Hypothesis hB:is_smooth_function_space hNX hNY V evB.
Local Notation TA := (smooth_test_space hA).
Local Notation TB := (smooth_test_space hB).
Local Notation valueA := (smooth_test_value hA).
Local Notation valueB := (smooth_test_value hB).

(** Source for [test_zero_extension_member_exists]: each
    original test has an actual extended test with
    exactly its normalized values on V, supporting
    Federer 4.1.1, p. 345. *)
Lemma test_zero_extension_member_exists (f:TA):
  exists g:TB,forall x,V x ->valueB g x=valueA f x.
Proof.
have [K hK]:=smooth_test_support_bound hA f.
pose KV:=@smooth_compact_domain_inclusion R X NX hNX U V hUV K.
have hGlobal:=@smooth_compact_zero_extension_regular R X Y NX NY hNX hNY U A evA hA
  K (smooth_test_inclusion hA f) hK.
have hClass:norm_class_all_orders hNX hNY V (valueA f).
  move=>k.
  exact:(@norm_class_open_restriction R X Y NX NY hNX hNY (fun _=>True) V (valueA f) k
    (fun _ _=>Logic.I) hV (hGlobal k)).
have hZero x:~SmoothCompactSet.smooth_compact_carrier KV x ->valueA f x=0.
  exact:((smooth_function_compact_support_iff hA K (smooth_test_inclusion hA f)).1 hK x).
exact (@smooth_test_represents_compact_function R X Y NX NY hNX hNY V B evB hB KV
  (valueA f) hClass hZero).
Qed.

(** Source for [test_zero_extension_member]: private choice
    of the proved extended test, supporting Federer
    4.1.1, p. 345. *)
Definition test_zero_extension_member f:TB:=projT1 (cid (test_zero_extension_member_exists f)).

(** Source for [test_zero_extension_member_value]: exact
    values of the proved extension on V, supporting
    Federer 4.1.1, p. 345. *)
Lemma test_zero_extension_member_value f x:V x ->
  valueB (test_zero_extension_member f) x=valueA f x.
Proof. exact:(projT2 (cid (test_zero_extension_member_exists f)) x). Qed.

(** Source for [test_zero_extension_member_linear]: extending
    by zero is linear, Federer 4.1.1, p. 345. *)
Lemma test_zero_extension_member_linear:linear test_zero_extension_member.
Proof.
move=>c f g; apply:(smooth_test_values_extensional hB)=>x hx.
have hAlinear:valueA (c*:f+g) x=c*:valueA f x+valueA g x:=congr1 (fun q:X->Y=>q x) (@smooth_test_values_linear R X Y NX NY hNX hNY U A evA hA c f g).
have hBlinear:valueB (c*:test_zero_extension_member f+test_zero_extension_member g) x=
    c*:valueB (test_zero_extension_member f) x+valueB (test_zero_extension_member g) x:=
  congr1 (fun q:X->Y=>q x) (@smooth_test_values_linear R X Y NX NY hNX hNY V B evB hB
  c (test_zero_extension_member f) (test_zero_extension_member g)).
rewrite (test_zero_extension_member_value (c*:f+g) hx) hBlinear
  (test_zero_extension_member_value f hx) (test_zero_extension_member_value g hx).
exact hAlinear.
Qed.

(** Source for [test_zero_extension_exists]: the actual
    linear zero-extension operator exists with the
    independent original-value and zero-value laws,
    Federer 4.1.1, p. 345. *)
Theorem test_zero_extension_exists:
  exists L:Hom TA TB,is_test_zero_extension U V valueA valueB L.
Proof.
exists (@HomMap R TA TB test_zero_extension_member
  (introT (asboolP _) test_zero_extension_member_linear)); constructor.
- move=>f x hx; exact:(test_zero_extension_member_value f (@hUV x hx)).
- move=>f x hx hNo; rewrite (test_zero_extension_member_value f hx).
  exact:(@smooth_test_value_outside R X Y NX NY hNX hNY U A evA hA f x hNo).
Qed.
End TestZeroExtensionExistence.
