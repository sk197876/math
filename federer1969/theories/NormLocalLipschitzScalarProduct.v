(** Federer (1969), 4.1.14, p. 371: localise the original
    locally Lipschitz map by a smooth compact cutoff before
    differentiating its smoothing. The supporting product estimate
    uses only the distance definition of 2.2.7, p. 64. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra ring.
From Federer Require Import RealNormUP NormMetric NormClassOneUP
  NormClassOneLocalLipschitz NormBoundedLinearTopology LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_scalar_product_lipschitz_bound]: multiplication
    by a locally bounded scalar cutoff preserves a finite local
    Lipschitz bound, supporting Federer 4.1.14, p. 371. *)
Theorem norm_scalar_product_lipschitz_bound (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (chi:X->R^o) (f:X->Y) a b L M:
  0<=a ->0<=b ->
  @is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space (@scalar_absolute_value_norm R)) A chi L ->
  @is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) A f M ->
  (forall x,A x->`|chi x|<=a) ->(forall x,A x->NY (f x)<=b) ->
  @is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) A (fun x=>chi x*:f x) (a*M+L*b).
Proof.
move=>ha hb hChi hF hChiBound hFBound;split.
- exact:addr_ge0 (mulr_ge0 ha hF.1) (mulr_ge0 hChi.1 hb).
- move=>x y hx hy.
  change (is_true (NY (chi x*:f x-chi y*:f y)<=(a*M+L*b)*NX (x-y))).
  have hSplit:chi x*:f x-chi y*:f y=
      chi x*:(f x-f y)+(chi x-chi y)*:f y.
    by rewrite scalerBr scalerBl addrA subrK.
  rewrite hSplit.
  have hTriangle:=real_seminorm_triangle hNY.1
    (chi x*:(f x-f y)) ((chi x-chi y)*:f y).
  rewrite !(real_seminorm_scale hNY.1) in hTriangle.
  have hFirst:`|chi x|*NY (f x-f y)<=a*(M*NX (x-y)).
    apply:(le_trans (ler_wpM2r (real_seminorm_nonnegative hNY.1 (f x-f y))
      (hChiBound x hx))).
    exact:(ler_wpM2l ha (hF.2 x y hx hy)).
  have hSecond:`|chi x-chi y|*NY (f y)<=(L*NX (x-y))*b.
    apply:(le_trans (ler_wpM2r (real_seminorm_nonnegative hNY.1 (f y))
      (hChi.2 x y hx hy))).
    exact:(ler_wpM2l (mulr_ge0 hChi.1 (real_seminorm_nonnegative hNX.1 (x-y)))
      (hFBound y hy)).
  have hCost:a*(M*NX (x-y))+(L*NX (x-y))*b=(a*M+L*b)*NX (x-y) by ring.
  rewrite -hCost;exact:(le_trans hTriangle (lerD hFirst hSecond)).
Qed.

(** Source for [norm_class_one_locally_metric_lipschitz]: the
    local Lipschitz bound of a smooth cutoff, supporting Federer
    4.1.14, p. 371, by the preceding differential bound in
    3.1.11, p. 222. The source and target norms are arbitrary. *)
Theorem norm_class_one_locally_metric_lipschitz (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (f:X->Y):
  norm_class_one NX NY U f ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U f.
Proof.
move=>hClass a ha.
have[C [d [hC [hd [hDomain hBound]]]]]:=
  @norm_class_one_local_lipschitz R X Y NX NY hNX hNY U f a ha hClass.
pose W:set X:=[set x|NX (x-a)<d].
have hW:nbhs (a:real_norm_metric_space hNX) W.
  apply:(metricType_numDomainType.nbhs_mdistP (a:real_norm_metric_space hNX) W).2.
  exists d;first exact:hd.
  move=>x hx;change (is_true (NX (a-x)<d)) in hx.
  change (is_true (NX (x-a)<d)).
  have hSymmetry:NX (x-a)=NX (a-x):=real_seminorm_subtract hNX.1 x a.
  by rewrite hSymmetry.
exists W;split;first exact:hW.
exists C;split;first exact:hC.
split;first exact:ltW hC.
move=>x y [_ hx] [_ hy];exact:hBound x y hx hy.
Qed.

(** Source for [norm_locally_lipschitz_scalar_product]: the original
    locally Lipschitz map times a locally Lipschitz scalar cutoff is
    locally Lipschitz on its original domain, used in Federer
    4.1.14, p. 371. No global image or global input bound is assumed. *)
Theorem norm_locally_lipschitz_scalar_product (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (chi:X->R^o) (f:X->Y):
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space (@scalar_absolute_value_norm R)) U chi ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U f ->
  @is_locally_metric_lipschitz R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) U (fun x=>chi x*:f x).
Proof.
move=>hChi hF a ha.
have[VC [hVC [L [hL hChiBound]]]]:=hChi a ha.
have[VF [hVF [M [hM hFBound]]]]:=hF a ha.
pose B:set X:=[set x|NX (x-a)<1].
have hB:nbhs (a:real_norm_metric_space hNX) B.
  apply:(metricType_numDomainType.nbhs_mdistP (a:real_norm_metric_space hNX) B).2.
  exists 1;first exact:ltr01.
  move=>x hx;change (is_true (NX (a-x)<1)) in hx.
  change (is_true (NX (x-a)<1)).
  have hSymmetry:NX (x-a)=NX (a-x):=real_seminorm_subtract hNX.1 x a.
  by rewrite hSymmetry.
pose W:=(VC `&` VF) `&` B.
have hW:nbhs (a:real_norm_metric_space hNX) W:=filterI (filterI hVC hVF) hB.
have hVCa:VC a:=nbhs_singleton hVC.
have hVFa:VF a:=nbhs_singleton hVF.
pose A:=`|chi a|+L.
pose Bf:=NY (f a)+M.
have hA:0<=A:=addr_ge0 (normr_ge0 _) (ltW hL).
have hBf:0<=Bf:=addr_ge0 (real_seminorm_nonnegative hNY.1 _) (ltW hM).
have hChiRestricted:@is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space (@scalar_absolute_value_norm R)) (U `&` W) chi L.
  apply:(@metric_lipschitz_bound_restrict R (real_norm_metric_space hNX)
    (real_norm_metric_space (@scalar_absolute_value_norm R)) (U `&` VC)
    (U `&` W) chi L _ hChiBound).
  move=>x [hx [[hvc _] _]];by split.
have hFRestricted:@is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) (U `&` W) f M.
  apply:(@metric_lipschitz_bound_restrict R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) (U `&` VF) (U `&` W) f M _ hFBound).
  move=>x [hx [[_ hvf] _]];by split.
have hChiNorm:forall x,(U `&` W) x->`|chi x|<=A.
  move=>x [hx [[hvc _] hNear]].
  have hDifference:=hChiBound.2 x a (conj hx hvc) (conj ha hVCa).
  change (is_true (`|chi x-chi a|<=L*NX (x-a))) in hDifference.
  have hSmall:=ler_wpM2l (ltW hL) (ltW hNear).
  rewrite mulr1 in hSmall.
  have hTriangle:=ler_normD (chi x-chi a) (chi a).
  rewrite subrK in hTriangle;rewrite /A;nra.
have hFNorm:forall x,(U `&` W) x->NY (f x)<=Bf.
  move=>x [hx [[_ hvf] hNear]].
  have hDifference:=hFBound.2 x a (conj hx hvf) (conj ha hVFa).
  change (is_true (NY (f x-f a)<=M*NX (x-a))) in hDifference.
  have hSmall:=ler_wpM2l (ltW hM) (ltW hNear).
  rewrite mulr1 in hSmall.
  have hTriangle:=real_seminorm_triangle hNY.1 (f x-f a) (f a).
  rewrite subrK in hTriangle;rewrite /Bf;nra.
have hProduct:=@norm_scalar_product_lipschitz_bound R X Y NX NY hNX hNY
  (U `&` W) chi f A Bf L M hA hBf hChiRestricted hFRestricted hChiNorm hFNorm.
exists W;split;first exact:hW.
pose C:=A*M+L*Bf+1.
have hC:0<C by rewrite /C;have h:=hProduct.1;lra.
exists C;split;first exact:hC.
apply:(@metric_lipschitz_bound_increase R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) (U `&` W) (fun x=>chi x*:f x) (A*M+L*Bf) C hProduct _).
by rewrite /C lerDl.
Qed.
