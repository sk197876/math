(** Federer (1969), 3.2.35, p. 271:
    inner and outer radial bounds for the
    actual gauge of a bounded open convex body.
    These support its corrected radial parametrization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets lra.
From Federer Require Import RealNormUP MinkowskiGaugeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_minkowski_gauge_inner_ball_bound]:
    supporting upper gauge bound for the radial
    boundary map in Federer 3.2.35, p. 271.
    A norm ball of radius r inside S
    gives g(x)<=N(x)/r by the actual infimum
    laws. The auxiliary positive rescaling is local;
    neither a boundary minimum nor convexity is used. *)
Lemma norm_minkowski_gauge_inner_ball_bound (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) g r:
  is_minkowski_gauge S g ->0<r ->(forall y:V,N y<r ->S y) ->
  forall x:V,g x<=N x/r.
Proof.
move=>hG hr hBall x; apply/ler_addgt0Pr=>e he.
have hNx:0<=N x:=real_seminorm_nonnegative hN.1 x.
have hRatio:0<=N x/r:=divr_ge0 hNx (ltW hr).
pose t:R:=N x/r+e.
have ht:0<t by rewrite /t; lra.
have hInv:0<t^-1 by rewrite invr_gt0.
have hStrict:N x/r<t by rewrite /t ltrDl.
have hProduct:N x<r*t.
  by move:hStrict; rewrite ltr_pdivrMr // mulrC.
have hSmall:N (t^-1*:x)<r.
  rewrite (real_seminorm_scale hN.1) (ger0_norm (ltW hInv)) mulrC.
  by rewrite ltr_pdivrMr.
exact:(@minkowski_gauge_lower R V S g hG x t ht (hBall _ hSmall)).
Qed.

(** Source for [norm_minkowski_gauge_outer_ball_bound]:
    supporting positive lower bound for g on
    the unit sphere in Federer 3.2.35,
    p. 271. An outer norm bound M
    on the original S gives N(x)/M<=g(x).
    This follows for every positive original
    rescaling before its infimum is taken. *)
Lemma norm_minkowski_gauge_outer_ball_bound (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (S:set V) g M:
  is_minkowski_gauge S g ->0<M ->(forall y:V,S y ->N y<=M) ->
  forall x:V,N x/M<=g x.
Proof.
move=>hG hM hBound x.
apply:(@minkowski_gauge_greatest R V S g hG x (N x/M)).
move=>t ht hS.
have hInv:0<t^-1 by rewrite invr_gt0.
have hb:=hBound _ hS.
rewrite (real_seminorm_scale hN.1) (ger0_norm (ltW hInv)) mulrC in hb.
rewrite ler_pdivrMr //.
by move:hb; rewrite ler_pdivrMr // mulrC.
Qed.
