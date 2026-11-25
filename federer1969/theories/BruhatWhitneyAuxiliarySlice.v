(** Federer (1969), 3.4.10, p. 338:
    the auxiliary equation of the cited surface
    has an analytic solution with prescribed (x,z)
    coordinates near each nonzero axis value.
    Apply the existing zero-slice coordinate theorem
    to its actual joint analytic inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations
  EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex EuclideanBlockLinearMaps
  NormDifferentialUP NormOpenDomainLaws NormDiffeomorphismUP NormAnalyticUP
  NormAnalyticLocal NormCoordinateSystemUP PrescribedAnalyticSliceCoordinates
  BruhatWhitneyAuxiliaryEquation BruhatWhitneyAuxiliaryInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bruhat_whitney_auxiliary_slice]: the
    actual local implicit solution used for the
    negative-axis regularity in the example cited by
    3.4.10, p. 338. Prescribed coordinates,
    the original equation and uniqueness among all
    nearby original solutions are proved by the
    existing coordinate-system laws. *)
Theorem bruhat_whitney_auxiliary_slice (R:realType) (b:R):
  let X:=R_n R 3 in
  let Y:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 3) in
  let NY:=inner_norm (@euclidean_inner_productP R 2) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3) in
  let hNY:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  let a:=@bruhat_whitney_auxiliary_point R b in
  let P:=@euclidean_first_block_map R 2 1 in
  b!=0 ->exists W:set X,exists V:set Y,exists psi:Y->X,
    @open (real_norm_metric_space hNX) W /\W a /\
    @open (real_norm_metric_space hNY) V /\V (P a) /\is_inner_convex V /\
    @norm_analytic R Y X NY NX hNY hNX V psi /\
    (forall u,V u ->P (psi u)=u /\@bruhat_whitney_auxiliary_equation R (psi u)=0) /\
    forall x,W x ->@bruhat_whitney_auxiliary_equation R x=0 ->psi (P x)=x.
Proof.
move=>X Y NX NY hNX hNY a P hb.
have [H [G [r [hFirst [hLast [hH [hR [hRT [hInverse hG]]]]]]]]]:=
  @bruhat_whitney_auxiliary_joint_inverse R b hb.
pose T:set X:=[set x|NX (x-a)<r].
pose C:set X:=H @` T.
pose B:set X:=[set x|@bruhat_whitney_auxiliary_equation R x=0].
have haB:B a:=@bruhat_whitney_auxiliary_point_zero R b hb.
have haT:T a by change (NX (a-a)<r);rewrite /NX subrr inner_norm0.
have hTa:=@norm_open_ball_domain_interior R X NX hNX a r a haT.
have hPlane x:T x ->(B x<->@euclidean_last_block_map R 2 1 (H x)=0).
  move=>hx;split.
  - move=>hZero;apply/ffunP=>i.
    by rewrite hLast hZero ffunE.
  - move=>hZero;have hAt:=congr1 (fun z:R_n R 1=>z ord0) hZero.
    by rewrite hLast ffunE in hAt.
have hPrefix x:T x ->P x=@euclidean_first_block_map R 2 1 (H x).
  by move=>_;rewrite hFirst.
have [W [V [psi [haW [hWT [hConvex [hPAnalytic [hPsiAnalytic hCoordinates]]]]]]]]:=
  @prescribed_analytic_slice_coordinates R 2 1 B T C H G P a
    haB hTa hInverse hG hPlane hPrefix.
exists W,V,psi;split;first exact:norm_analytic_domain_open hPAnalytic.
split;first exact:haW.
split;first exact:norm_analytic_domain_open hPsiAnalytic.
split;first exact:(@norm_coordinate_forward_range R X Y NX NY hNX hNY
  B W V P psi 1%N hCoordinates a haW).
split;first exact:hConvex.
split;first exact:hPsiAnalytic.
split.
- move=>u hu;split;first exact:(@norm_coordinate_cancel R X Y NX NY hNX hNY
    B W V P psi 1%N hCoordinates u hu).
  exact:(@norm_coordinate_backward_membership R X Y NX NY hNX hNY
    B W V P psi 1%N hCoordinates u hu).1.
- move=>x hx hEquation;exact:(@norm_coordinate_base_inverse R X Y NX NY hNX hNY
    B W V P psi 1%N hCoordinates x hEquation hx).
Qed.
