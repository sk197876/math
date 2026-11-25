(** Federer (1969), 4.1.8, p. 360: nearby parameter
    slices have a common compact support in the first variables.
    This supporting whole-space translation bound reuses the compact
    thickening proved for the regularisation in 4.1.2, p. 347. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis SmoothCompactSet
  SmoothCompactThickening SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation SmoothGlobalTranslationSealed
  TestGlobalTranslation TestGlobalTranslationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestTranslationCommonSupport.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation L := (@SmoothGlobalTranslation.operator R X Y NX NY hNX hNY E ev hE).
Local Notation hL := (@SmoothGlobalTranslation.laws R X Y NX NY hNX hNY E ev hE).
Local Notation A := (fun c=>@test_global_translation R X Y NX NY hNX hNY E ev hE c (L c) (hL c)).

(** Source for [test_translation_common_support]: a test and
    all its translates by vectors of norm at most one have
    one compact support bound. This supports the continuity
    of the original slice in Federer 4.1.8, p. 360. *)
Theorem test_translation_common_support (f:DT):
  exists C:smooth_compact_set hNX (fun _=>True),forall c,NX c<=1 ->
    @smooth_function_support R X Y NX hNX (fun _=>True) E ev (inc (A c f))
      `<=` smooth_compact_carrier C.
Proof.
have[K hK]:=smooth_test_support_bound hE f.
have[C [_ hNear]]:=@smooth_compact_thickening R X NX hNX d b hb K 1 ler01.
have hOff:forall z,~smooth_compact_carrier K z->ev (inc f) z=0.
  exact:(smooth_function_compact_support_iff hE K (inc f)).1 hK.
exists C=>c hc.
apply:(smooth_function_compact_support_iff hE C _).2=>x hx.
rewrite (@test_global_translation_values R X Y NX NY hNX hNY E ev hE c f x).
apply:(@hOff (x+c)).
move=>hKxc; apply:hx; apply:(hNear x (x+c) hKxc).
have hDiff:x-(x+c)=-c by rewrite opprD addrA subrr add0r.
by rewrite hDiff (real_seminorm_negate hNX.1).
Qed.
End TestTranslationCommonSupport.
