(** Federer (1969), 4.1.7, p. 356: actual
    constant smooth coefficient fields used in the
    original coordinate and current identities.
    The public law is independent of a construction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity NormRegularityOperations
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothConstantUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothConstantExistence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable U:X->Prop.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.

(** Source for [smooth_constant_member_exists]: the
    original constant field is smooth and belongs
    to E, supporting Federer 4.1.7, p. 356. *)
Lemma smooth_constant_member_exists c:exists f:E,forall x,U x->ev f x=c.
Proof.
apply:(smooth_function_evaluation_surjective hE).
move=>k;exact:(@norm_class_constant R X Y NX NY hNX hNY U c k hU).
Qed.

(** Source for [smooth_constant_member]: private witness
    used only to prove existence of the original
    constant-field map, supporting Federer 4.1.7,
    p. 356. *)
Definition smooth_constant_member c:E:=projT1 (cid (smooth_constant_member_exists c)).

(** Source for [smooth_constant_member_value]: exact
    original value of the private witness, supporting
    Federer 4.1.7, p. 356. *)
Lemma smooth_constant_member_value c x:U x->ev (smooth_constant_member c) x=c.
Proof. exact:(projT2 (cid (smooth_constant_member_exists c)) x). Qed.

(** Source for [smooth_constant_member_linear]: original
    constant fields respect vector operations,
    supporting Federer 4.1.7, p. 356. *)
Lemma smooth_constant_member_linear:linear smooth_constant_member.
Proof.
move=>a c d;apply:(smooth_function_extensional hE)=>x hx.
rewrite (smooth_constant_member_value (a*:c+d) hx)
  (smooth_function_add_value hE) (smooth_function_scale_value hE)
  (smooth_constant_member_value c hx) (smooth_constant_member_value d hx).
reflexivity.
Qed.

(** Source for [smooth_constant_operator_exists]: the
    independently specified original constant-field
    map exists, supporting Federer 4.1.7, p. 356. *)
Theorem smooth_constant_operator_exists:
  exists L:Hom Y E,is_smooth_constant_operator U ev L.
Proof.
exists (@HomMap R Y E smooth_constant_member (introT (asboolP _) smooth_constant_member_linear)).
exact:smooth_constant_member_value.
Qed.
End SmoothConstantExistence.
