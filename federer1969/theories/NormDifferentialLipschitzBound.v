(** Federer (1969), 3.2.3, p. 244: the graph
    differential has norm at most Lip(f)+epsilon. This
    supporting bound for Df follows from the directional
    difference quotients of 3.1.1, p. 209. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_global_lipschitz_bound]:
    the differential norm bound used for the graph map
    in Federer 3.2.3, p. 244, proved from the
    actual differential and a global pairwise bound. *)
Lemma norm_differential_global_lipschitz_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (f:X->Y) a (D:Hom X Y) M:
  has_norm_differential NX NY (fun _=>True) f a D ->
  (forall x y,NY (f x-f y)<=M*NX (x-y)) -> forall v,NY (D v)<=M*NX v.
Proof.
move=>hD hLip v; apply/negPn/negP=>hBad.
have hExcess:M*NX v<NY (D v) by rewrite ltNge.
pose e:=(NY (D v)-M*NX v)/2.
have he:0<e by rewrite /e divr_gt0 // subr_gt0.
have [d [hd hNear]]:=norm_differential_directional_limit hNX hNY hD v he.
pose t:=d/2.
have ht:0<t by rewrite /t divr_gt0.
have htN:`|t|<d by rewrite ger0_norm // /t; nra.
have hArg:0<`|t|<d by apply/andP; split; first by rewrite normr_gt0 gt_eqF.
have hError:=hNear t hArg.
pose q:=t^-1 *: (f (a+t*:v)-f a).
have hBound:NY q<=M*NX v.
  rewrite /q (real_seminorm_scale hNY.1).
  have hb:=hLip (a+t*:v) a.
  have hSub:(a+t*:v)-a=t*:v by rewrite (addrC a (t*:v)) addrK.
  rewrite hSub (real_seminorm_scale hNX.1) in hb.
  have hScaled:=ler_wpM2l (normr_ge0 (t^-1)) hb.
  refine (le_trans hScaled _).
  rewrite normfV !(ger0_norm (ltW ht)).
  have ht0:t!=0 by rewrite gt_eqF.
  have hCancel:t^-1*(t*NX v)=NX v by rewrite mulrA (mulVf ht0) mul1r.
  by rewrite (mulrCA (t^-1) M (t*NX v)) hCancel.
have hTri:=real_seminorm_triangle hNY.1 (D v-q) q.
rewrite subrK (real_seminorm_subtract hNY.1 (D v) q) in hTri.
change (is_true (NY (q-D v)<e)) in hError.
rewrite /e in hError; nra.
Qed.
