(** Federer (1969), 3.4.2(8), p. 315: choose small
    compact coordinate cubes inside the original open chart image. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra ring.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP NormDifferentialUP
  EuclideanCoordinateCubeUP EuclideanCoordinateCubeGeometry EuclideanCoordinateMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_local_coordinate_cube_exists]: the
    contained cubes A+B used in 3.4.2(8), p. 315. Every
    original open-domain point lies in the interior of a
    positive-side compact coordinate cube contained in that
    domain. The empty coordinate family is retained. *)
Theorem critical_local_coordinate_cube_exists (R:realType) n
    (U:set (R_n R n)) (a:R_n R n):
  norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U a ->
  exists u r Q,0<r /\is_euclidean_coordinate_cube u r Q /\Q `<=` U /\
    norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) Q a.
Proof.
move=>[delta [hDelta hInside]].
pose N:=inner_norm (@euclidean_inner_productP R n).
pose r:=delta/(n%:R+1).
have hDen:0<(n%:R+1:R) by have hh:=ler0n R n;lra.
have hr:0<r by rewrite /r divr_gt0.
pose u:R_n R n:=[ffun i=>a i-r/2].
have [Q hQ]:=euclidean_coordinate_cube_exists u (ltW hr).
have haQ:Q a.
  apply:(hQ.2 a).2=>i;rewrite /u ffunE.
  have hHalf:0<r/2 by rewrite divr_gt0 // ltr0n.
  have hDouble:r/2+r/2=r by field.
  apply/andP;split;lra.
have hRadius:n%:R*r<delta.
  have hExact:(n%:R+1)*r=delta by rewrite /r;field;by rewrite gt_eqF.
  have hExpand:(n%:R+1)*r=n%:R*r+r by ring.
  rewrite hExpand in hExact;lra.
exists u,r,Q;split;first exact:hr.
split;first exact:hQ.
split.
- move=>x hx.
  have hBound:=@coordinate_cube_distance_bound R n u r Q hQ x a hx haQ.
  have hSmall:N (x-a)<delta:=le_lt_trans hBound hRadius.
  have hActual:=hInside (x-a) hSmall.
  by rewrite addrC subrK in hActual.
- exists (r/2);split;first by rewrite divr_gt0 // ltr0n.
  move=>v hv;apply:(hQ.2 (a+v)).2=>i.
  have hBound:=euclidean_coordinate_norm_bound i v.
  have hSmall:`|v i|<r/2:=le_lt_trans hBound hv.
  rewrite ltr_norml in hSmall.
  have /andP[hNegative hPositive]:=hSmall.
  rewrite /u !ffunE.
  have hDouble:r/2+r/2=r by field.
  apply/andP;split;lra.
Qed.
