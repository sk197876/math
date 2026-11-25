(** Federer (1969), 4.1.8, p. 360: translating a test in
    the second set of variables supports the original smooth-slice
    argument. These supporting identities concern the actual test
    operators already constructed for 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothTestEvaluation SmoothGlobalTranslationSealed
  TestGlobalTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TestGlobalTranslationLaws.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation L := (@SmoothGlobalTranslation.operator R X Y NX NY hNX hNY E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R X Y NX NY hNX hNY E ev hE).
Local Notation A := (fun c=>@test_global_translation R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).

(** Source for [test_global_translation_values]: the actual
    translated test has value f(x+c), supporting the slice map
    in Federer 4.1.8, p. 360, by the original translation
    convention in 4.1.1, p. 346. *)
Theorem test_global_translation_values c (f:DT) x:
  ev (inc (A c f)) x=ev (inc f) (x+c).
Proof.
rewrite (@test_global_translation_inclusion R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).
exact:hL.
Qed.

(** Source for [test_global_translation_zero]: zero translation
    is the identity on actual test functions, supporting the
    slice argument of Federer 4.1.8, p. 360. *)
Theorem test_global_translation_zero (f:DT):A 0 f=f.
Proof.
apply:(smooth_test_values_extensional hE)=>x _.
change (ev (inc (A 0 f)) x=ev (inc f) x).
by rewrite test_global_translation_values addr0.
Qed.

(** Source for [test_global_translation_composition]: successive
    translations add their vectors on the original test space,
    supporting the variable slice of Federer 4.1.8, p. 360. *)
Theorem test_global_translation_composition c d (f:DT):
  A c (A d f)=A (c+d) f.
Proof.
apply:(smooth_test_values_extensional hE)=>x _.
change (ev (inc (A c (A d f))) x=ev (inc (A (c+d) f)) x).
by rewrite !test_global_translation_values addrA.
Qed.
End TestGlobalTranslationLaws.
