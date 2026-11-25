(** Federer (1969), 4.1.1, p. 346: differentiation preserves
    a compact support bound. This proves that the actual smooth
    derivative operator acts on the test-function spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothDerivativeSupport SmoothDirectionalDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section DirectionalSupport.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evZ := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable v:X.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P.
Local Notation support := (@smooth_function_support R X Y NX hNX U E ev).

(** Source for [smooth_directional_derivative_preserves_compact_support]:
    D_j maps D_K(U,Y) into itself, supporting the distribution
    derivatives of Federer 4.1.1, p. 346. This includes the
    zero direction and empty compact support. *)
Theorem smooth_directional_derivative_preserves_compact_support
    (K:smooth_compact_set hNX U) f:
  support f `<=` smooth_compact_carrier K ->
  support (P f) `<=` smooth_compact_carrier K.
Proof.
move=>hf; apply:(smooth_function_compact_support_iff hE K (P f)).2=>x hx.
case:(pselect (U x))=>[hUx|hUx]; last exact:(smooth_function_evaluation_outside hE (P f) hUx).
rewrite (hP f hUx).
rewrite (@smooth_derivative_outside_compact_support R X Y NX NY hNX hNY U hU E ev hE D hD
  K f hf 1%N x hx).
exact:linear0.
Qed.
End DirectionalSupport.
