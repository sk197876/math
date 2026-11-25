(** Federer (1969), 4.1.1, p. 346: actual
    translations of globally smooth functions exist.
    Existence reuses affine smoothness and composition
    from 3.1.11 rather than adding calculus axioms. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP NormOpenDomainLaws NormRegularity NormRegularityOperations
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothGlobalTranslationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section GlobalTranslationExistence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Variable c:X.

(** Source for [smooth_global_translation_regular]: translation
    preserves every finite smoothness class, supporting
    the original quotient in Federer 4.1.1,
    p. 346. *)
Lemma smooth_global_translation_regular f:
  norm_class_all_orders hNX hNY (fun _=>True) (fun x=>ev f (x+c)).
Proof.
move=>k.
have hFull x (_:True):norm_domain_interior NX (fun _=>True) x:=norm_full_domain_interior NX x.
have hIdBound:norm_bounded_linear NX NX (hom_of_linear (linear_id X)).
  exists 1; split; first exact:ler01; by move=>x; rewrite mul1r.
have hId:=@norm_class_linear R X X NX NX hNX hNX (fun _=>True) (hom_of_linear (linear_id X)) k hFull hIdBound.
have hC:=@norm_class_constant R X X NX NX hNX hNX (fun _=>True) c k hFull.
have hAffine:=norm_class_add hId hC.
exact:(@norm_class_compose_on R X X Y NX NX NY hNX hNX hNY
  (fun _=>True) (fun _=>True) (fun x=>x+c) (ev f) k
  (fun _ _=>Logic.I) hAffine (smooth_function_evaluation_smooth hE f k)).
Qed.

(** Source for [smooth_global_translation_member_exists]: the
    translated values have a representative in E,
    supporting Federer 4.1.1, p. 346. *)
Lemma smooth_global_translation_member_exists f:
  exists g:E,forall x,ev g x=ev f (x+c).
Proof.
have [g hg]:=smooth_function_evaluation_surjective hE (smooth_global_translation_regular f).
exists g=>x; exact:(hg x Logic.I).
Qed.

(** Source for [smooth_global_translation_member]: private
    choice of the proved representative, hidden
    behind the translation seal for Federer 4.1.1,
    p. 346. *)
Definition smooth_global_translation_member f:E:=projT1 (cid (smooth_global_translation_member_exists f)).

(** Source for [smooth_global_translation_member_value]: the
    chosen representative retains exactly the shifted
    values, supporting Federer 4.1.1, p. 346. *)
Lemma smooth_global_translation_member_value f x:
  ev (smooth_global_translation_member f) x=ev f (x+c).
Proof. exact:(projT2 (cid (smooth_global_translation_member_exists f)) x). Qed.

(** Source for [smooth_global_translation_linear]: translation
    is linear in the smooth function, supporting
    the test quotient in Federer 4.1.1,
    p. 346. *)
Lemma smooth_global_translation_linear:linear smooth_global_translation_member.
Proof.
move=>t f g; apply:(smooth_function_extensional hE)=>x hx.
by rewrite smooth_global_translation_member_value (smooth_function_add_value hE)
  (smooth_function_scale_value hE) (smooth_function_add_value hE) (smooth_function_scale_value hE)
  !smooth_global_translation_member_value.
Qed.

(** Source for [smooth_global_translation_exists]: an actual
    linear operator satisfies the independent value
    laws, supporting Federer 4.1.1, p. 346. *)
Theorem smooth_global_translation_exists:
  exists L:Hom E E,is_smooth_global_translation ev c L.
Proof.
exists (@HomMap R E E smooth_global_translation_member
  (introT (asboolP _) smooth_global_translation_linear)).
exact:smooth_global_translation_member_value.
Qed.
End GlobalTranslationExistence.
