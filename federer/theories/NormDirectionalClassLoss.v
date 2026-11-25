(** Federer (1969), 4.1.2, p. 347: each
    differentiation of a class-(k+1) input leaves a
    class-k field. This adapter uses the actual
    derivative-field regularity and bounded directional evaluation
    already proved in 3.1.11, p. 221. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousMultilinearSealed
  NormRegularity NormRegularityOperations NormRegularityLinearMaps NormRegularityDerivativeField SmoothDirectionalEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_directional_class_loss]: the original
    derivative regularity used in the iteration
    D^i(Phi*f)=Phi*D^i f, Federer 4.1.2,
    p. 347, by 3.1.11, p. 221. *)
Theorem norm_directional_class_loss (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (f:X->Y) (D:X->Hom X Y) v k:
  norm_class hNX hNY (fun _=>True) f k.+1 ->
  (forall x,has_norm_differential NX NY (fun _=>True) f x (D x)) ->
  norm_class hNX hNY (fun _=>True) (fun x=>D x v) k.
Proof.
move=>hClass hD.
pose Z:=@ContinuousMultilinear.space R 1%N X Y NX NY hNX hNY.
pose ZN:=@ContinuousMultilinear.norm R 1%N X Y NX NY hNX hNY.
pose ev:=@ContinuousMultilinear.evaluation R 1%N X Y NX NY hNX hNY.
pose hZ:=@ContinuousMultilinear.laws R 1%N X Y NX NY hNX hNY.
pose hZN:=continuous_multilinear_norm_is_norm hNY hZ.
have [G [hG hActual]]:=@norm_class_derivative_field R X Y NX NY hNX hNY
  (fun _=>True) f k hClass.
have hField:=@norm_class_postcompose_linear R X Z Y NX ZN NY hNX hZN hNY
  (fun _=>True) G (ev [ffun _:'I_1=>v]) k
  (@first_derivative_directional_evaluation_bound R X Y NX NY hNX hNY v) hG.
apply:(norm_class_domain_agreement _ hField)=>x _.
have hSame:=norm_differential_unique hNX hNY (hActual x Logic.I) (hD x).
exact:(congr1 (fun L:Hom X Y=>L v) hSame).
Qed.
