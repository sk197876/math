(** Federer (1969), 4.1.1, p. 346: first derivatives of
    smooth functions are smooth. Reuse the precise class-loss
    theorem of 3.1.11, p. 221, for the actual supplied derivative
    field rather than rebuilding the calculus. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm NormClassHigherUP NormClassHigherDerivative NormRegularity
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section FirstDerivativeRegularity.
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
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hZ 1%N)).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.

(** Source for [smooth_first_derivative_field_regular]: each
    finite class of the original first derivative field follows
    from the next class of f, supporting the smooth derivative
    operators of Federer 4.1.1, p. 346. *)
Theorem smooth_first_derivative_field_regular f k:
  norm_class hNX hN1 U (fun x=>@D 1%N x f) k.
Proof.
have hf:=smooth_function_evaluation_smooth hE f k.+1.
have hf':@norm_class_higher R X Y NX NY Z evZ ZN U (ev f) (1+k)%N.
  by rewrite add1n.
exact:(@norm_class_higher_derivative_field R 1%N k X Y NX NY hNX hNY Z evZ ZN hZ
  (fun j=>@ContinuousMultilinear.space R j X (Z 1%N) NX (@ZN 1%N) hNX hN1)
  (fun j=>@ContinuousMultilinear.evaluation R j X (Z 1%N) NX (@ZN 1%N) hNX hN1)
  (fun j=>@ContinuousMultilinear.norm R j X (Z 1%N) NX (@ZN 1%N) hNX hN1)
  (fun j=>@ContinuousMultilinear.laws R j X (Z 1%N) NX (@ZN 1%N) hNX hN1)
  U (ev f) (fun x=>@D 1%N x f) hf'
  (fun x hx=>@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD 1%N f x hx)).
Qed.
End FirstDerivativeRegularity.
