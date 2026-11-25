(** Federer (1969), 4.1.7, p. 356: actual
    constant coefficient fields have zero directional
    derivative. Use the original first differential
    and the checked smooth evaluation law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear NormDifferentialLocal
  ContinuousMultilinearSealed SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionDerivativesUP
  SmoothConstantUP SmoothDirectionalDerivativeUP SmoothDirectionalOrdinary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [smooth_constant_directional_zero]:
    actual D_v of an original constant field is
    zero, supporting the coordinate current identities
    of Federer 4.1.7, p. 356. *)
Theorem smooth_constant_directional_zero (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (hU:forall x,U x->norm_domain_interior NX U x)
    (E:lmodType R) (ev:E->X->Y) (hE:is_smooth_function_space hNX hNY U ev)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    (L:Hom Y E) (hL:is_smooth_constant_operator U ev L) v (P:Hom E E)
    (hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P) c:
  P (L c)=0.
Proof.
apply:(smooth_function_extensional hE)=>x hx.
have hConst:=@norm_differential_constant R X Y NX NY hNX hNY U x c (@hU x hx).
have hActual:has_norm_differential NX NY U (ev (L c)) x 0.
  exact:(norm_differential_domain_agreement hNX (fun y hy=>esym (@hL c y hy)) hConst).
have hValue:=@smooth_directional_ordinary_evaluation R X Y NX NY hNX hNY U E ev D hD
  v P hP (L c) x 0 hx hActual.
by rewrite hValue hom_zeroE (smooth_function_zero_value hE).
Qed.
