(** Federer (1969), 4.1.2, p. 347: the tests
    x maps to psi(x-z)y used to define the
    smooth dual density. Their original values specify
    them independently of any realization construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section TranslatedKernelTest.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).

(** Source for [is_translated_kernel_tests]: the exact
    compactly supported test in the displayed definition of
    g_epsilon in Federer 4.1.2, p. 347. *)
Definition is_translated_kernel_tests (psi:X->R) (B:X->Hom Y DT):Prop:=
  forall z y x,smooth_test_value hE (B z y) x=psi (x-z)*:y.

(** Source for [translated_kernel_tests_unique]: the tests
    defining the dual density in Federer 4.1.2,
    p. 347, are unique by their original values. *)
Theorem translated_kernel_tests_unique psi (B C:X->Hom Y DT):
  is_translated_kernel_tests psi B ->is_translated_kernel_tests psi C ->B=C.
Proof.
move=>hB hC; apply:funext=>z; apply:hom_ext=>y.
apply:(smooth_test_values_extensional hE)=>x _.
by rewrite hB hC.
Qed.
End TranslatedKernelTest.
