(** Federer (1969), 3.4.2(7), p. 314: restrict the local
    inverse of the joint map to its scalar-zero slice. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormClassOneUP
  NormRegularity NormRegularityOperations NormFiniteLinearBound NormLinearDomainLaws
  NormOpenDomainLaws NormDiffeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_joint_zero_slice]: the inverse on the
    level F=0 in 3.4.2(7), p. 314. A small convex open ball in
    q coordinates lies in the inverse image domain. Restricting
    the local inverse to j(u) gives the section, its class k,
    and both inverse identities on the original zero level.
    The construction also treats a zero-dimensional q target. *)
Theorem critical_joint_zero_slice (R:realType) n r k
    (q:Hom (R_n R n) (R_n R r)) (j:Hom (R_n R r) (R_n R n))
    (F:R_n R n->R) v (D E:set (R_n R n)) (h:R_n R n->R_n R n) a:
  cancel j q ->q v=0 ->v!=0 ->D a ->F a=0 ->
  is_norm_diffeomorphism
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) D E
    (fun x=>j (q x)+F x*:v) h k ->
  exists radius:R,0<radius /\
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R r))
      (inner_norm_real_norm (@euclidean_inner_productP R n))
      [set u|inner_norm (@euclidean_inner_productP R r) (u-q a)<radius]
      (fun u=>h (j u)) k /\
    (forall u,inner_norm (@euclidean_inner_productP R r) (u-q a)<radius ->
      D (h (j u)) /\q (h (j u))=u /\F (h (j u))=0) /\
    forall x,D x ->F x=0 ->
      inner_norm (@euclidean_inner_productP R r) (q x-q a)<radius ->h (j (q x))=x.
Proof.
move=>hSection hV hv ha hFa hD.
pose X:=R_n R n;pose W:=R_n R r.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose NW:=inner_norm (@euclidean_inner_productP R r).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose hNW:=inner_norm_real_norm (@euclidean_inner_productP R r).
pose G:=fun x=>j (q x)+F x*:v.
have hProjection x:q (G x)=q x.
  change (q (j (q x)+F x*:v)=q x).
  by rewrite (Bilinear.linD (hom_linear q)) hSection
    (Bilinear.linZ (hom_linear q)) hV scaler0 addr0.
have hBase:E (j (q a)).
  have hh:=norm_diffeomorphism_maps hD ha.
  by rewrite hFa scale0r addr0 in hh.
have hInterior:norm_domain_interior NX E (j (q a)):=
  (norm_class_continuous (norm_diffeomorphism_inverse_class hD) hBase).1.
have hJBound:=@norm_finite_linear_bounded R W X NW NX hNW hNX r
  (@coordinate_basis R r) (@coordinate_basisP R r) j.
have [radius [hRadius hBall]]:=@norm_bounded_linear_preimage_interior R W X NW NX
  hNW j E (q a) hJBound hInterior.
pose U:=fun u=>NW (u-q a)<radius.
have hMap u (hu:U u):E (j u).
  have hh:=hBall (u-q a) hu.
  by rewrite (addrC (q a) (u-q a)) subrK in hh.
have hUInterior u (hu:U u):norm_domain_interior NW U u.
  exact:(@norm_open_ball_domain_interior R W NW hNW (q a) radius u hu).
have hJClass:=@norm_class_linear R W X NW NX hNW hNX U j k hUInterior hJBound.
have hClass:=norm_class_compose_on hMap hJClass (norm_diffeomorphism_inverse_class hD).
exists radius;split;first exact:hRadius.
split;first exact:hClass.
split.
- move=>u hu.
  have hAt:E (j u):=hMap u hu.
  have hSource:D (h (j u)):=norm_diffeomorphism_inverse_maps hD hAt.
  have hEqual:G (h (j u))=j u:=norm_diffeomorphism_right_inverse hD hAt.
  have hQ:q (h (j u))=u.
    have hh:=congr1 q hEqual.
    by rewrite hProjection hSection in hh.
  have hScalar:F (h (j u))*:v=0.
    have hh:=congr1 (fun w=>w-j u) hEqual.
    by rewrite /G hQ addrAC !subrr add0r in hh.
  have hZero:F (h (j u))=0.
    apply/eqP;move/eqP:hScalar;by rewrite scaler_eq0 (negbTE hv) orbF.
  split;first exact:hSource.
  by split.
- move=>x hx hFx hSmall.
  have hh:=norm_diffeomorphism_left_inverse hD hx.
  by rewrite hFx scale0r addr0 in hh.
Qed.
