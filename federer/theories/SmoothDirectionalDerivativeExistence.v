(** Federer (1969), 4.1.1, p. 346: the directional
    derivative is an actual linear endomorphism of E(U,Y).
    Existence follows from smoothness of the actual derivative
    evaluation and the abstract smooth-space representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed SmoothFunctionSpaceUP
  SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP SmoothDirectionalDerivativeUP
  SmoothDirectionalEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section DirectionalDerivativeExistence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evZ := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable v:X.
Local Notation q := (fun f x=>@evZ 1%N [ffun _: 'I_1=>v] (@D 1%N x f)).

(** Source for [smooth_directional_derivative_member_exists]:
    the actual directional derivative has a representative in
    E(U,Y), supporting the operators in Federer 4.1.1, p. 346. *)
Lemma smooth_directional_derivative_member_exists f:
  exists g:E,forall x,U x -> ev g x=q f x.
Proof.
exact:(smooth_function_evaluation_surjective hE
  (smooth_directional_evaluation_regular hE hD f v)).
Qed.

(** Source for [smooth_directional_derivative_member]: private
    choice of the proved derivative representative, supporting
    Federer 4.1.1, p. 346. It is hidden behind the operator seal. *)
Definition smooth_directional_derivative_member f:E:=
  projT1 (cid (smooth_directional_derivative_member_exists f)).

(** Source for [smooth_directional_derivative_member_value]: the
    chosen representative has exactly the original derivative
    values on U, supporting Federer 4.1.1, p. 346. *)
Lemma smooth_directional_derivative_member_value f x:
  U x -> ev (smooth_directional_derivative_member f) x=q f x.
Proof. exact:(projT2 (cid (smooth_directional_derivative_member_exists f)) x). Qed.

(** Source for [smooth_directional_derivative_linear]: the
    derivative operator is linear in the smooth function,
    supporting D_j in Federer 4.1.1, p. 346. This follows from
    linearity of the already proved first differential. *)
Lemma smooth_directional_derivative_linear:
  linear smooth_directional_derivative_member.
Proof.
move=>c f g; apply:(smooth_function_extensional hE)=>x hx.
rewrite (smooth_directional_derivative_member_value (c*:f+g) hx)
  (smooth_function_add_value hE) (smooth_function_scale_value hE)
  (smooth_directional_derivative_member_value f hx)
  (smooth_directional_derivative_member_value g hx).
by rewrite !linearP.
Qed.

(** Source for [smooth_directional_derivative_exists]: the
    independently specified original derivative endomorphism
    exists, supporting Federer 4.1.1, p. 346. No vector topology
    of D is assumed or used in this existence proof. *)
Theorem smooth_directional_derivative_exists:
  exists P:Hom E E,
    @is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P.
Proof.
exists (@HomMap R E E smooth_directional_derivative_member
  (introT (asboolP _) smooth_directional_derivative_linear)).
exact:smooth_directional_derivative_member_value.
Qed.
End DirectionalDerivativeExistence.
