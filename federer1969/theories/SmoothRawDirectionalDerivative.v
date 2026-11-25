(** Federer (1969), 4.1.2, p. 347: every
    directional derivative of a smooth scalar kernel
    is smooth. This raw-function adapter reuses the
    derivative-field class law and bounded evaluation
    already proved in 3.1.11 and 4.1.1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousMultilinearSealed
  NormRegularity NormRegularityOperations NormRegularityLinearMaps NormRegularityDerivativeField SmoothDirectionalEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothRawDirectionalDerivative.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable f:X->Y.
Variable D:X->Hom X Y.
Hypothesis hSmooth:norm_class_all_orders hNX hNY (fun _=>True) f.
Hypothesis hD:forall x,has_norm_differential NX NY (fun _=>True) f x (D x).
Local Notation Z := (@ContinuousMultilinear.space R 1%N X Y NX NY hNX hNY).
Local Notation ZN := (@ContinuousMultilinear.norm R 1%N X Y NX NY hNX hNY).
Local Notation ev := (@ContinuousMultilinear.evaluation R 1%N X Y NX NY hNX hNY).
Local Notation hZ := (@ContinuousMultilinear.laws R 1%N X Y NX NY hNX hNY).
Local Notation hZN := (continuous_multilinear_norm_is_norm hNY hZ).

(** Source for [smooth_raw_directional_derivative]: differentiating
    the scalar kernel leaves a smooth kernel,
    supporting the iteration in Federer 4.1.2, p. 347.
    The supplied field is the actual differential. *)
Theorem smooth_raw_directional_derivative v:
  norm_class_all_orders hNX hNY (fun _=>True) (fun x=>D x v).
Proof.
move=>k.
have [G [hG hActual]]:=@norm_class_derivative_field R X Y NX NY hNX hNY
  (fun _=>True) f k (hSmooth k.+1).
have hClass:=@norm_class_postcompose_linear R X Z Y NX ZN NY hNX hZN hNY
  (fun _=>True) G (ev [ffun _:'I_1=>v]) k
  (@first_derivative_directional_evaluation_bound R X Y NX NY hNX hNY v) hG.
apply:(norm_class_domain_agreement _ hClass)=>x _.
have hSame:=norm_differential_unique hNX hNY (hActual x Logic.I) (hD x).
have hEval:=congr1 (fun L:Hom X Y=>L v) hSame.
exact hEval.
Qed.
End SmoothRawDirectionalDerivative.
