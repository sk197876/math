(** Federer (1969), 4.1.1, p. 345: actual smooth
    restriction between open domains exists and is linear.
    The proof uses the original class restriction theorem
    and the independent smooth-space representation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothRestrictionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothRestrictionExistence.
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

(** Source for [smooth_restriction_member_exists]: every
    smooth function on V restricts to a represented
    smooth function on U, supporting Federer 4.1.1,
    p. 345. *)
Lemma smooth_restriction_member_exists f:
  exists g:A,forall x,U x ->evA g x=evB f x.
Proof.
apply:(smooth_function_evaluation_surjective hA)=>k.
exact:(@norm_class_open_restriction R X Y NX NY hNX hNY V U (evB f) k hUV hU
  (@smooth_function_evaluation_smooth R X Y NX NY hNX hNY V B evB hB f k)).
Qed.

(** Source for [smooth_restriction_member]: private choice
    of the proved restriction representative, supporting
    Federer 4.1.1, p. 345. *)
Definition smooth_restriction_member (f:B):A:=projT1 (cid (smooth_restriction_member_exists f)).

(** Source for [smooth_restriction_member_value]: exact
    restriction values on U, supporting Federer
    4.1.1, p. 345. *)
Lemma smooth_restriction_member_value f x:U x ->
  evA (smooth_restriction_member f) x=evB f x.
Proof. exact:(projT2 (cid (smooth_restriction_member_exists f)) x). Qed.

(** Source for [smooth_restriction_member_linear]: restriction
    is linear, supporting the original open-set dual
    maps in Federer 4.1.1, p. 345. *)
Lemma smooth_restriction_member_linear:linear smooth_restriction_member.
Proof.
move=>c f g; apply:(smooth_function_extensional hA)=>x hx.
rewrite (smooth_restriction_member_value (c*:f+g) hx)
  !(smooth_function_add_value hA) !(smooth_function_scale_value hA)
  !(smooth_function_add_value hB) !(smooth_function_scale_value hB)
  (smooth_restriction_member_value f hx) (smooth_restriction_member_value g hx).
reflexivity.
Qed.

(** Source for [smooth_restriction_exists]: the actual
    linear restriction operator exists with its independent
    pointwise law, supporting Federer 4.1.1, p. 345. *)
Theorem smooth_restriction_exists:exists L:Hom B A,is_smooth_restriction U evA evB L.
Proof.
exists (@HomMap R B A smooth_restriction_member
  (introT (asboolP _) smooth_restriction_member_linear)).
exact:smooth_restriction_member_value.
Qed.
End SmoothRestrictionExistence.
