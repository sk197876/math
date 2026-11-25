(** Federer (1969), 3.4.11, p. 338:
    the positive first-coordinate direction is an actual
    tangent to the original cusp. Use the original
    polynomial points (t^2,t^3) and the already proved
    norm and tangent-cone laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra ring.
From Federer Require Import RealNormUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness TangentConeUP TangentConeBasic AnalyticCuspUP AnalyticCuspSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cusp_positive_axis_tangent]: the
    direction (1,0) is an actual tangent to
    the original cusp, as printed in 3.4.11,
    p. 338. The witnesses lie on the
    original equation, with both printed strict bounds. *)
Theorem analytic_cusp_positive_axis_tangent (R:realType):
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R 2))
    (@AnalyticCusp.set R) 0 (@coordinate_basis R 2 ord0).
Proof.
pose X:=R_n R 2.
pose NX:=inner_norm (@euclidean_inner_productP R 2).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R 2).
pose e0:=@coordinate_basis R 2 ord0.
pose e1:=@coordinate_basis R 2 ord_max.
move=>e he.
pose A:=NX e0;pose B:=NX e1.
have hA:0<=A:=real_seminorm_nonnegative hNX.1 e0.
have hB:0<=B:=real_seminorm_nonnegative hNX.1 e1.
pose t:=e/(2*(A+B+e+1)).
have hDen:0<2*(A+B+e+1) by nra.
have ht:0<t by rewrite /t divr_gt0.
have ht0:t!=0 by rewrite (gt_eqF ht).
have hProduct:t*(2*(A+B+e+1))=e by rewrite /t divfK ?gt_eqF.
have ht1:t<1 by nra.
have hT2:0<t^+2:=exprn_gt0 _ ht.
have hT3:0<t^+3:=exprn_gt0 _ ht.
have hT2Bound:t^+2<=t by rewrite expr2;nra.
have hT3Bound:t^+3<=t.
  have hCube:t^+3=t^+2*t by ring.
  rewrite hCube;have h:=ler_wpM2r (ltW ht) hT2Bound.
  rewrite -expr2 in h;exact:le_trans h hT2Bound.
pose x:X:=t^+2*:e0+t^+3*:e1.
have hCoordinates:x ord0=t^+2 /\x ord_max=t^+3.
  rewrite /x /e0 /e1 /coordinate_basis !ffunE /=.
  change (t^+2*1+t^+3*0=t^+2 /\t^+2*0+t^+3*1=t^+3).
  by rewrite !mulr0 !mulr1 ?addr0 ?add0r.
have hx:@AnalyticCusp.set R x.
  apply/(@AnalyticCusp.laws R).
  rewrite hCoordinates.1 hCoordinates.2;ring.
have hNorm:NX x<e.
  have hTriangle:=real_seminorm_triangle hNX.1 (t^+2*:e0) (t^+3*:e1).
  rewrite !(real_seminorm_scale hNX.1) (ger0_norm (ltW hT2))
    (ger0_norm (ltW hT3)) in hTriangle.
  change (is_true (NX x<=t^+2*A+t^+3*B)) in hTriangle.
  nra.
pose r:=(t^+2)^-1.
have hr:0<r by rewrite /r invr_gt0.
have hScale:r*:x-e0=t*:e1.
  have hR2:r*t^+2= 1 by rewrite /r mulVf ?expf_eq0 ?ht0.
  have hR3:r*t^+3=t.
    rewrite /r;field;rewrite ?expf_eq0 ?ht0 //.
  by rewrite /x scalerDr !scalerA hR2 hR3 scale1r addrAC subrr add0r.
exists x,r;split;first exact:hx.
split;first exact:hr.
rewrite subr0;split;first exact:hNorm.
rewrite hScale (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)).
change (is_true (t*B<e));nra.
Qed.
