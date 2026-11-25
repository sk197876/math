(** Federer (1969), 4.1.7, pp. 355–356: the
    original smooth coefficient operators exist.
    Their existence follows from the earlier bounded
    linear calculus and actual smooth-space realization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  NormSmoothPostcompose SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothTargetOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothTargetOperatorExistence.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:X->Prop.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Variable L:Hom Y Z.
Hypothesis hL:norm_bounded_linear NY NZ L.

(** Source for [smooth_target_member_exists]: the
    coefficient image is an actual smooth field,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma smooth_target_member_exists f:
  exists g:F,forall x,U x->fv g x=L (ev f x).
Proof.
apply:(smooth_function_evaluation_surjective hF).
exact:(@norm_smooth_postcompose R X Y Z NX NY NZ hNX hNY hNZ U (ev f) L hL
  (smooth_function_evaluation_smooth hE f)).
Qed.

(** Source for [smooth_target_member]: private choice
    of the proved original coefficient image,
    supporting Federer 4.1.7, pp. 355–356. *)
Definition smooth_target_member f:F:=projT1 (cid (smooth_target_member_exists f)).

(** Source for [smooth_target_member_value]: exact
    original values of the private representative,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma smooth_target_member_value f x:
  U x->fv (smooth_target_member f) x=L (ev f x).
Proof. exact:(projT2 (cid (smooth_target_member_exists f)) x). Qed.

(** Source for [smooth_target_member_linear]: fixed
    coefficient maps are linear on smooth fields,
    supporting Federer 4.1.7, pp. 355–356. *)
Lemma smooth_target_member_linear:linear smooth_target_member.
Proof.
move=>c f g; apply:(smooth_function_extensional hF)=>x hx.
rewrite (smooth_target_member_value (c*:f+g) hx)
  (smooth_function_add_value hE) (smooth_function_scale_value hE)
  (smooth_function_add_value hF) (smooth_function_scale_value hF)
  (smooth_target_member_value f hx) (smooth_target_member_value g hx).
by rewrite linearP.
Qed.

(** Source for [smooth_target_operator_exists]: the
    independently specified smooth coefficient operator
    exists, supporting Federer 4.1.7, pp. 355–356. *)
Theorem smooth_target_operator_exists:
  exists P:Hom E F,is_smooth_target_operator U ev fv L P.
Proof.
exists (@HomMap R E F smooth_target_member (introT (asboolP _) smooth_target_member_linear)).
exact:smooth_target_member_value.
Qed.
End SmoothTargetOperatorExistence.
