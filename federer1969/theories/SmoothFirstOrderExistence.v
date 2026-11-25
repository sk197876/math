(** Federer (1969), 4.1.7, p. 356: actual
    smooth first-order operators exist. Reuse the
    original derivative regularity and bounded linear
    target composition from 3.1.11, pp. 219–221. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  ContinuousMultilinearSealed ContinuousMultilinearNorm SmoothFunctionSpaceUP
  SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP SmoothFirstDerivativeRegularity
  NormSmoothPostcompose SmoothFirstOrderUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothFirstOrderExistence.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:X->Prop.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation JN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hJ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hJ 1%N)).
Variable D:forall j,X->Hom E (J j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable M:Hom (J 1%N) Z.
Hypothesis hM:norm_bounded_linear (@JN 1%N) NZ M.

(** Source for [smooth_first_order_member_exists]: the
    original first-order field is an actual member
    of the target smooth space, supporting Federer
    4.1.7, p. 356. *)
Lemma smooth_first_order_member_exists f:
  exists g:F,forall x,U x->fv g x=M (@D 1%N x f).
Proof.
apply:(smooth_function_evaluation_surjective hF).
apply:(@norm_smooth_postcompose R X (J 1%N) Z NX (@JN 1%N) NZ hNX hN1 hNZ
  U (fun x=>@D 1%N x f) M hM).
exact:(smooth_first_derivative_field_regular hE hD f).
Qed.

(** Source for [smooth_first_order_member]: private
    choice of the proved smooth representative,
    supporting Federer 4.1.7, p. 356. *)
Definition smooth_first_order_member f:F:=projT1 (cid (smooth_first_order_member_exists f)).

(** Source for [smooth_first_order_member_value]: exact
    original values of the selected representative,
    supporting Federer 4.1.7, p. 356. *)
Lemma smooth_first_order_member_value f x:
  U x->fv (smooth_first_order_member f) x=M (@D 1%N x f).
Proof. exact:(projT2 (cid (smooth_first_order_member_exists f)) x). Qed.

(** Source for [smooth_first_order_member_linear]: the
    original first-order operation is linear,
    supporting Federer 4.1.7, p. 356. *)
Lemma smooth_first_order_member_linear:linear smooth_first_order_member.
Proof.
move=>c f g; apply:(smooth_function_extensional hF)=>x hx.
rewrite (smooth_first_order_member_value (c*:f+g) hx)
  (smooth_function_add_value hF) (smooth_function_scale_value hF)
  (smooth_first_order_member_value f hx) (smooth_first_order_member_value g hx).
by rewrite !linearP.
Qed.

(** Source for [smooth_first_order_operator_exists]: the
    independently specified original first-order
    operator exists, supporting Federer 4.1.7, p. 356. *)
Theorem smooth_first_order_operator_exists:
  exists P:Hom E F,is_smooth_first_order_operator U fv D M P.
Proof.
exists (@HomMap R E F smooth_first_order_member
  (introT (asboolP _) smooth_first_order_member_linear)).
exact:smooth_first_order_member_value.
Qed.
End SmoothFirstOrderExistence.
