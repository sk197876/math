(** Federer (1969), 3.1.24, p. 238: choosing
    the common closed ball for the homogeneous coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology lra.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP HomogeneousPolynomialFunctions
  NormPolynomialCoefficientBall NormSeriesTermBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_analytic_coefficients_common_ball]: the
    choice of r>0 at the start of (4) to (1),
    Federer 3.1.24, p. 238. Uniform convergence bounds
    the late coefficients; continuity and positive homogeneity
    bound the finite prefix after shrinking the ball. The
    actual domain contains the entire resulting closed ball. *)
Lemma norm_analytic_coefficients_common_ball (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:X->Prop) (f:X->Y) (P:nat->X->Y) a :
  norm_domain_interior NX U a ->
  (forall m,@is_homogeneous_polynomial R X Y m (P m) /\
    continuous (fun x:real_norm_metric_space hNX=>(P m x:real_norm_metric_space hNY))) ->
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    forall x,U x -> NY (f x-\sum_(m<N.+1) P m (x-a))<eps) ->
  exists r:R,0<r /\ (forall v,NX v<=r -> U (a+v)) /\
    forall m,(1<=m)%N -> forall v,NX v<=r -> NY (P m v)<=1.
Proof.
move=>[r0 [hr0 hU]] hP hc.
have [n hn]:=@norm_uniform_series_late_terms R X Y NY hNY.1 U f
  (fun m x=>P m (x-a)) hc.
have [d [hd hb]]:=@norm_finite_polynomial_coefficients_ball R X Y NX NY hNX hNY P n hP.
pose r:=Num.min r0 d/2.
have hmin:0<Num.min r0 d by rewrite lt_min hr0 hd.
have hr:0<r by rewrite /r divr_gt0 // ltr0n.
have hrmin:r<Num.min r0 d by rewrite /r; lra.
have hrr0:r<r0.
  apply: lt_le_trans hrmin _; by rewrite ge_min lexx.
have hrd:r<d.
  apply: lt_le_trans hrmin _; by rewrite ge_min lexx orbT.
exists r; split; first exact hr.
split; first by move=>v hv; exact (hU v (le_lt_trans hv hrr0)).
move=>m hm v hv.
case hmn:(m<=n)%N.
- have hmi:(0<m<=n)%N by rewrite hm hmn.
  exact (hb m hmi v (le_lt_trans hv hrd)).
- have hnm:(n<m)%N by rewrite ltnNge hmn.
  have hx:U (a+v):=hU v (le_lt_trans hv hrr0).
  have hh:=hn m hnm (a+v) hx.
  by rewrite addrAC subrr add0r in hh.
Qed.
