(** Federer (1969), 3.4.2(6), p. 312: a finite Lipschitz bound on
    the original compact tube controls its interior differentials. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [critical_local_lipschitz_differential_bound]: supporting
    the bound for g'(t) in 3.4.2(6), p. 312. A pairwise Lipschitz bound
    on a set B controls the actual differential at its interior points.
    The differentiable domain A may differ from B; both contain a
    neighbourhood of the point. Follow the directional quotient proof
    of 3.1.1, retaining arbitrary normed source and target spaces. *)
Theorem critical_local_lipschitz_differential_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A B:X->Prop) (f:X->Y) a (D:Hom X Y) M:
  has_norm_differential NX NY A f a D ->norm_domain_interior NX B a ->
  (forall x y,B x ->B y ->NY (f x-f y)<=M*NX (x-y)) ->
  forall v,NY (D v)<=M*NX v.
Proof.
move=>hD hInterior hLip v;apply/negPn/negP=>hBad.
have hGap:M*NX v<NY (D v) by rewrite ltNge.
pose e:=(NY (D v)-M*NX v)/2.
have he:0<e by rewrite /e divr_gt0 // subr_gt0.
have [d [hd hNear]]:=norm_differential_directional_limit hNX hNY hD v he.
have haB:B a:=norm_domain_interior_member hNX hInterior.
have [r [hr hBall]]:=hInterior.
have hNorm:0<=NX v:=real_seminorm_nonnegative hNX.1 v.
have hDen:0<NX v+1 by lra.
pose t:=Num.min d (r/(NX v+1))/2.
have hMin:0<Num.min d (r/(NX v+1)) by rewrite lt_min hd divr_gt0.
have ht:0<t by rewrite /t divr_gt0.
have hHalf:t<Num.min d (r/(NX v+1)) by rewrite /t;lra.
have htD:t<d.
  apply:(lt_le_trans hHalf);by rewrite ge_min lexx.
have htR:t<r/(NX v+1).
  apply:(lt_le_trans hHalf);by rewrite ge_min lexx orbT.
have htNorm:t*NX v<r.
  have h:=htR;rewrite (ltr_pdivlMr _ _ hDen) in h;nra.
have hPoint:B (a+t*:v).
  apply:hBall;by rewrite (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)).
have hArg:0<`|t|<d by rewrite (ger0_norm (ltW ht));apply/andP;split.
have hError:=hNear t hArg.
pose q:=t^-1*:(f (a+t*:v)-f a).
have hBound:NY q<=M*NX v.
  rewrite /q (real_seminorm_scale hNY.1).
  have hb:=hLip (a+t*:v) a hPoint haB.
  have hSub:(a+t*:v)-a=t*:v by rewrite (addrC a (t*:v)) addrK.
  rewrite hSub (real_seminorm_scale hNX.1) in hb.
  have hh:=ler_wpM2l (normr_ge0 (t^-1)) hb.
  apply:(le_trans hh).
  rewrite normfV !(ger0_norm (ltW ht)).
  have ht0:t!=0 by rewrite gt_eqF.
  have hCancel:t^-1*(t*NX v)=NX v by rewrite mulrA (mulVf ht0) mul1r.
  by rewrite (mulrCA (t^-1) M (t*NX v)) hCancel.
have hTriangle:=real_seminorm_triangle hNY.1 (D v-q) q.
rewrite subrK (real_seminorm_subtract hNY.1 (D v) q) in hTriangle.
change (is_true (NY (q-D v)<e)) in hError.
rewrite /e in hError;nra.
Qed.
