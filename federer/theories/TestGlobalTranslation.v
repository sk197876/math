(** Federer (1969), 4.1.1, p. 346: the
    translated globally supported test is an actual
    member of D. Its compact support is proved
    before taking an opaque subspace lift. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP LinearSubspaceRepresentationUP LinearSubspaceLiftSealed
  SmoothCompactSet SmoothCompactTranslate SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothTestSubspaces SmoothTestSpaces SmoothGlobalTranslationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section TestGlobalTranslation.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Variable c:X.
Variable L:Hom E E.
Hypothesis hL:is_smooth_global_translation ev c L.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).

(** Source for [test_global_translation_member]: translation
    preserves compact support, supporting the test
    quotient in Federer 4.1.1, p. 346. *)
Lemma test_global_translation_member f:
  smooth_compact_support_subspace hE (hom_comp L inc f).
Proof.
have [K hK]:=subspace_representation_member (smooth_test_space_laws hE) f.
exists (smooth_compact_translate K c).
apply:(smooth_function_compact_support_iff hE _ _).2=>x hx.
rewrite hom_compE hL.
exact:((smooth_function_compact_support_iff hE K (inc f)).1 hK (x+c) hx).
Qed.

(** Source for [test_global_translation]: actual translated
    test function with its proved compact support,
    supporting Federer 4.1.1, p. 346. *)
Definition test_global_translation:Hom DT DT:=
  @LinearSubspaceLift.map R DT DT E (smooth_compact_support_subspace hE) inc
    (smooth_test_space_laws hE) (hom_comp L inc) test_global_translation_member.

(** Source for [test_global_translation_inclusion]: the
    test translation agrees with the original
    smooth translation, supporting Federer 4.1.1,
    p. 346. *)
Theorem test_global_translation_inclusion f:
  inc (test_global_translation f)=L (inc f).
Proof. exact:LinearSubspaceLift.evaluation. Qed.
End TestGlobalTranslation.
