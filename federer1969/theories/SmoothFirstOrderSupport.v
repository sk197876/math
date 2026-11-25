(** Federer (1969), 4.1.7, p. 356: the
    exterior derivative preserves the original compact
    support bound. This supporting first-order law
    reuses derivative locality from 4.1.1, p. 345. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothDerivativeSupport SmoothFirstOrderUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothFirstOrderSupport.
Variable R:realType.
Variables X Y Z:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NZ:Z->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variables E F:lmodType R.
Variables (ev:E->X->Y) (fv:F->X->Z).
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Hypothesis hF:is_smooth_function_space hNX hNZ U fv.
Local Notation J := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Variable D:forall j,X->Hom E (J j).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable M:Hom (J 1%N) Z.
Variable P:Hom E F.
Hypothesis hP:is_smooth_first_order_operator U fv D M P.

(** Source for [smooth_first_order_preserves_support]:
    every original fixed compact-support step is
    preserved by the first-order operator, supporting
    Federer 4.1.7, p. 356. *)
Theorem smooth_first_order_preserves_support (K:smooth_compact_set hNX U) f:
  @smooth_function_support R X Y NX hNX U E ev f `<=` smooth_compact_carrier K ->
  @smooth_function_support R X Z NX hNX U F fv (P f) `<=` smooth_compact_carrier K.
Proof.
move=>hf; apply:(smooth_function_compact_support_iff hF K (P f)).2=>x hx.
case:(pselect (U x))=>[hUx|hUx].
- rewrite (@hP f x hUx).
  rewrite (@smooth_derivative_outside_compact_support R X Y NX NY hNX hNY U hU
    E ev hE D hD K f hf 1%N x hx).
  exact:linear0.
- exact:(smooth_function_evaluation_outside hF (P f) hUx).
Qed.
End SmoothFirstOrderSupport.
