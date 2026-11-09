(** Federer (1969), 3.4.5, p. 321: finite
    actual Taylor coefficients of an analytic function are
    analytic functions of its centre. This is used along
    the axis in the real proof of the cited local/global
    example and follows from 3.1.24, pp. 237–240. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormAnalyticUP NormAnalyticLinear NormAnalyticOperations
  NormOpenDomainLaws ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormHigherDifferentialUP NormHigherDifferentialUnique NormAnalyticHigherJet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_derivative_evaluation_exists]:
    actual fixed-argument derivative coefficient functions are
    analytic, supporting the example cited at 3.4.5, p. 321.
    Both the original recursive derivative equation and its
    analyticity are proved; no auxiliary field is assumed. *)
Theorem norm_analytic_derivative_evaluation_exists (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) k (u:{ffun 'I_k->X}):
  @norm_analytic R X Y NX NY hNX hNY A f ->
  exists g:X->Y,
    (forall x,A x ->forall z:@ContinuousMultilinear.space R k X Y NX NY hNX hNY,
      has_norm_higher_differential NX
        (fun i=>@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY)
        (fun i=>@ContinuousMultilinear.norm R i X Y NX NY hNX hNY) A f k x z ->
      g x=@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY u z) /\
    @norm_analytic R X Y NX NY hNX hNY A g.
Proof.
move=>hf.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose NZ i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
pose hNZ:=continuous_multilinear_norm_is_norm hNY (hZ k).
have [G [hG hAnalyticG]]:=@norm_analytic_higher_jet_exists R X Y NX NY hNX hNY k A f hf.
pose L:Hom (Z k) Y:=ev k u.
have hL:norm_bounded_linear (NZ k) NY L.
  exists (\prod_(i<k) NX (u i));split.
  - apply:prodr_ge0=>i _;exact:(real_seminorm_nonnegative hNX.1 (u i)).
  - move=>z;rewrite mulrC;exact:(multilinear_operator_bound (continuous_multilinear_norm_laws (hZ k) z) u).
have hAnalyticL:=@norm_bounded_linear_analytic R (Z k) Y (NZ k) NY hNZ hNY setT
  (fun z _=>norm_full_domain_interior _ z) L hL.
exists (fun x=>L (G x));split.
- move=>x hx z hz.
  have hEqual:=@norm_higher_differential_unique R X Y NX NY hNX hNY
    Z ev NZ hZ A f k x (G x) z (hG x hx) hz.
  by rewrite hEqual.
- exact:(norm_analytic_compose_on (fun x hx=>Logic.I) hAnalyticG hAnalyticL).
Qed.
