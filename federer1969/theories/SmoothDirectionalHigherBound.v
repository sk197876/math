(** Federer (1969), 4.1.1, p. 346: each higher derivative
    of a directional derivative has a finite bound by the next
    original derivative. This supports continuity without adding
    a hypothesis to the printed distribution operators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  ContinuousMultilinearSealed ContinuousMultilinearNorm ContinuousMultilinearPostcompose
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialLocal
  NormHigherDifferentialPostcompose SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDirectionalDerivativeUP SmoothDirectionalEvaluation SmoothFirstDerivativeGrouping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section DirectionalHigherBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evZ := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Local Notation hN1 := (continuous_multilinear_norm_is_norm hNY (hZ 1%N)).
Local Notation W := (fun k=>@ContinuousMultilinear.space R k X (Z 1%N) NX (@ZN 1%N) hNX hN1).
Local Notation evW := (fun k=>@ContinuousMultilinear.evaluation R k X (Z 1%N) NX (@ZN 1%N) hNX hN1).
Local Notation WN := (fun k=>@ContinuousMultilinear.norm R k X (Z 1%N) NX (@ZN 1%N) hNX hN1).
Local Notation hW := (fun k=>@ContinuousMultilinear.laws R k X (Z 1%N) NX (@ZN 1%N) hNX hN1).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable v:X.
Variable P:Hom E E.
Hypothesis hP:@is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P.

(** Source for [smooth_directional_higher_derivative_bound]: for
    each finite j one fixed constant controls D^j(P_v phi) by
    D^(j+1)phi throughout U, supporting the continuity asserted
    for distribution derivatives in Federer 4.1.1, p. 346.
    Exact grouping and bounded target composition are reused. *)
Theorem smooth_directional_higher_derivative_bound j:
  exists C:R,0<=C /\ forall f x,U x ->
    @ZN j (@D j x (P f))<=C * @ZN j.+1 (@D j.+1 x f).
Proof.
have [J [hJN hJ]]:=smooth_first_derivative_grouping_exists hD.
pose M:Hom (Z 1%N) Y:=@evZ 1%N [ffun _: 'I_1=>v].
have hM:=@first_derivative_directional_evaluation_bound R X Y NX NY hNX hNY v.
have [A [hA hAb]]:=@continuous_multilinear_postcompose_family_exists R X (Z 1%N) Y
  NX (@ZN 1%N) NY W Z evW WN evZ ZN hW hZ M hM.
have [C [hC hb]]:=hAb j.
exists C; split=>// f x hx.
have hField y hy:
    has_norm_higher_differential NX evW WN U (fun t=>@D 1%N t f) j y
      (J j (@D (1+j)%N y f)):=hJ j f y hy.
have hTarget:=@norm_higher_differential_field_postcompose R X (Z 1%N) Y
  NX (@ZN 1%N) NY hNX hN1 hNY W Z evW WN evZ ZN hW hZ M A hA hAb U
  (fun y=>@D 1%N y f) j (fun y=>J j (@D (1+j)%N y f)) hField x hx.
have hEq y (hy:U y) (_:U y):ev (P f) y=M (@D 1%N y f).
  rewrite /M; exact (hP f hy).
have hLocal:=@norm_higher_differential_local_agreement R X Y NX NY hNX hNY
  Z evZ ZN hZ j U U U (ev (P f)) (fun y=>M (@D 1%N y f)) hU
  (fun y hy=>iff_refl (U y)) hEq x hx (A j (J j (@D (1+j)%N x f))).
have hSame:=norm_higher_differential_unique hNX hNY hZ
  (@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD j (P f) x hx)
  (hLocal.2 hTarget).
rewrite hSame.
have hEst:=hb (J j (@D (1+j)%N x f)).
have hNormNext:@ZN (1+j)%N (@D (1+j)%N x f)=@ZN j.+1 (@D j.+1 x f).
  by rewrite add1n.
rewrite hJN hNormNext in hEst; exact hEst.
Qed.
End DirectionalHigherBound.
