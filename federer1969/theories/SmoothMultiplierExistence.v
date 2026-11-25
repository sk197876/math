(** Federer (1969), 4.1.1, p. 345: existence and linearity
    of multiplication by a smooth scalar function. The proof
    reuses the Chapter 3 scalar-times-vector class law and the
    independent smooth-space representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormRegularity NormRegularityBilinear
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothMultiplierUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section SmoothMultiplierExistence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u.

(** Source for [smooth_multiplier_member_exists]: the product
    u phi is actually represented in E(U,Y), supporting the
    scalar restriction of a distribution in Federer 4.1.1,
    p. 345. Arbitrary normed targets are retained. *)
Lemma smooth_multiplier_member_exists f:
  exists g:E,forall x,U x -> ev g x=u x*:ev f x.
Proof.
apply:(smooth_function_evaluation_surjective hE)=>k.
exact:(norm_class_scalar_product (hu k) (smooth_function_evaluation_smooth hE f k)).
Qed.

(** Source for [smooth_multiplier_member]: private choice of
    the proved product representative, supporting Federer
    4.1.1, p. 345. *)
Definition smooth_multiplier_member f:E:=
  projT1 (cid (smooth_multiplier_member_exists f)).

(** Source for [smooth_multiplier_member_value]: the selected
    product has exactly the original pointwise values on U,
    supporting Federer 4.1.1, p. 345. *)
Lemma smooth_multiplier_member_value f x:
  U x -> ev (smooth_multiplier_member f) x=u x*:ev f x.
Proof. exact:(projT2 (cid (smooth_multiplier_member_exists f)) x). Qed.

(** Source for [smooth_multiplier_linear]: multiplication by
    a fixed smooth scalar is linear, supporting T L v_s in
    Federer 4.1.1, p. 345. *)
Lemma smooth_multiplier_linear:linear smooth_multiplier_member.
Proof.
move=>c f g; apply:(smooth_function_extensional hE)=>x hx.
rewrite (smooth_multiplier_member_value (c*:f+g) hx)
  !(smooth_function_add_value hE) !(smooth_function_scale_value hE)
  (smooth_multiplier_member_value f hx) (smooth_multiplier_member_value g hx).
by rewrite scalerDr !scalerA mulrC.
Qed.

(** Source for [smooth_multiplier_exists]: the actual smooth
    scalar multiplication endomorphism exists with the independent
    evaluation law, supporting Federer 4.1.1, p. 345. *)
Theorem smooth_multiplier_exists:
  exists P:Hom E E,is_smooth_multiplier U ev u P.
Proof.
exists (@HomMap R E E smooth_multiplier_member (introT (asboolP _) smooth_multiplier_linear)).
exact:smooth_multiplier_member_value.
Qed.
End SmoothMultiplierExistence.
