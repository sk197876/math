(** Federer (1969), 4.1.14, p. 371: composition of
    the original compact Lipschitz images. Choose compatible
    smooth approximation domains: the first smooth maps land
    in the fixed source of the second smooth maps. Only
    f(K), rather than f(U), must lie in that smaller source.
    Existing sharp compact Lipschitz approximations prove
    existence; the original composite approximation law is
    a separate consequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity NormRegularityOperations InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct LipschitzUP
  OpenLocalLipschitzCompact SmoothCompactSet SmoothCompactInteriorThickening
  CurrentLipschitzCompactImage CurrentCompactSmoothApproximationUP
  CurrentCompactSmoothApproximationExistence CurrentCompactSmoothApproximationOriginal
  CurrentSmoothApproximationUP CurrentMapDifferential EuclideanHomOperator
  HomSpaceTopology CriticalLocalDerivativeBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentNestedSmoothApproximation.
Variable R:realType.
Variables n nu omega:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R omega).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R omega)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R omega)).
Variables (U:set X) (V:set Y) (W:set Z).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Hypothesis hW:forall z,W z->norm_domain_interior NZ W z.
Variables (f:X->Y) (g:Y->Z).
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall y,V y->W (g y).
Arguments hFImage : clear implicits.
Arguments hGImage : clear implicits.
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNY) (real_norm_metric_space hNZ) V g.
Variable K:smooth_compact_set hNX U.

(** Source for [current_nested_compact_smooth_approximations_exists]:
    compatible approximations for the two original maps in
    the composition assertion of Federer 4.1.14, p. 371.
    The intermediate compact E is a neighbourhood of f(K).
    The original f need not map all of U into the smaller
    open source Zg of the second smooth family. *)
Theorem current_nested_compact_smooth_approximations_exists:
  exists E:smooth_compact_set hNY V,
  exists Lf Lg:R,exists Zf:set X,exists Zg:set Y,
  exists a:nat->X->Y,exists b:nat->Y->Z,
    (forall x,smooth_compact_carrier K x->
      norm_domain_interior NY (smooth_compact_carrier E) (f x)) /\
    @is_current_compact_smooth_approximation R nu omega V W E g Lg Zg b /\
    @is_current_compact_smooth_approximation R n nu U Zg K f Lf Zf a.
Proof.
pose fK:=@current_lipschitz_compact_image R n nu U V hU
  f hFImage hFLocal K.
have[r [hr [E [hFE hTube]]]]:=@smooth_compact_interior_thickening R Y NY hNY
  nu (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInterior:forall x,smooth_compact_carrier K x->
    norm_domain_interior NY (smooth_compact_carrier E) (f x).
  move=>x hx;exists r;split;first exact:hr.
  move=>h hh;apply:(hTube (f x+h) (f x)).
  - change ((f @` smooth_compact_carrier K) (f x));by exists x.
  - rewrite [f x+h]addrC addrK;exact:ltW hh.
have hFInE:forall x,smooth_compact_carrier K x->smooth_compact_carrier E (f x).
  move=>x hx;exact:(@norm_domain_interior_member R Y NY hNY
    (smooth_compact_carrier E) (f x) (hInterior x hx)).
have[Lf hLf]:=@norm_open_local_lipschitz_compact R X Y NX NY hNX hNY U f
  (smooth_compact_carrier K) hU hFLocal (smooth_compact_is_compact K)
  (smooth_compact_in_domain K).
have[Lg hLg]:=@norm_open_local_lipschitz_compact R Y Z NY NZ hNY hNZ V g
  (smooth_compact_carrier E) hV hGLocal (smooth_compact_is_compact E)
  (smooth_compact_in_domain E).
have hGImageE:forall y,smooth_compact_carrier E y->W (g y).
  move=>y hy;exact:hGImage y (smooth_compact_in_domain E y hy).
have[Zg [b hB]]:=@current_compact_smooth_approximation_exists R nu omega V W
  hV hW E g Lg hLg.2 hGImageE.
pose hZg:=current_compact_smooth_domain_open hB.
have hFImageK:forall x,smooth_compact_carrier K x->Zg (f x).
  move=>x hx;exact:(@current_compact_smooth_domain_contains R nu omega
    V W E g Lg Zg b hB (f x) (hFInE x hx)).
have[Zf [a hA]]:=@current_compact_smooth_approximation_exists R n nu U Zg
  hU hZg K f Lf hLf.2 hFImageK.
exists E,Lf,Lg,Zf,Zg,a,b;by split;[exact:hInterior|split].
Qed.
End CurrentNestedSmoothApproximation.

Section CurrentNestedSmoothComposite.
Variable R:realType.
Variables n nu omega:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R omega).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R omega)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R omega)).
Variables (U:set X) (V:set Y) (W:set Z).
Variables (K:smooth_compact_set hNX U) (E:smooth_compact_set hNY V).
Variables (f:X->Y) (g:Y->Z) (Lf Lg:R) (Zf:set X) (Zg:set Y).
Variables (a:nat->X->Y) (b:nat->Y->Z).
Hypothesis hB:@is_current_compact_smooth_approximation R nu omega V W E g Lg Zg b.
Hypothesis hA:@is_current_compact_smooth_approximation R n nu U Zg K f Lf Zf a.
Hypothesis hFInE:forall x,smooth_compact_carrier K x->smooth_compact_carrier E (f x).
Arguments hFInE : clear implicits.
Local Notation hZf:=(current_compact_smooth_domain_open hA).
Local Notation hKZf:=(current_compact_smooth_domain_contains hA).
Local Notation KZf:=(@current_compact_index_in_open R n U Zf K hKZf).
Local Notation composite:=(fun i x=>b i (a i x)).

(** Source for [current_nested_smooth_composite_approximation]:
    the actual composed smooth maps form one of the original
    allowed approximation sequences for g composed with f,
    supporting Federer 4.1.14, p. 371. The derivative
    cap is Lg*Lf, and its proof uses only the common
    chosen source domains. No extra cap is imposed in the
    universal image specification. *)
Theorem current_nested_smooth_composite_approximation:
  @is_current_smooth_approximation R n omega Zf W KZf
    (fun x=>g (f x)) composite.
Proof.
have hLf:0<=Lf:=current_compact_smooth_bound_nonnegative hA.
have hLg:0<=Lg:=current_compact_smooth_bound_nonnegative hB.
have hSmooth:forall i,norm_class_all_orders hNX hNZ Zf (composite i).
  move=>i k.
  exact:(@norm_class_compose_on R X Y Z NX NY NZ hNX hNY hNZ
    Zf Zg (a i) (b i) k (current_compact_smooth_image hA i)
    (current_compact_smooth_class hA i k) (current_compact_smooth_class hB i k)).
have hLipschitz:forall i x y,Zf x->Zf y->
    NZ (composite i x-composite i y)<=(Lg*Lf)*NX (x-y).
  move=>i x y hx hy.
  have hAX:=current_compact_smooth_image hA i hx.
  have hAY:=current_compact_smooth_image hA i hy.
  have hFirst:NY (a i x-a i y)<=Lf*NX (x-y):=
    (current_compact_smooth_lipschitz hA i).2 x y hx hy.
  have hSecond:NZ (b i (a i x)-b i (a i y))<=Lg*NY (a i x-a i y):=
    (current_compact_smooth_lipschitz hB i).2 (a i x) (a i y) hAX hAY.
  have hScaled:=ler_wpM2l hLg hFirst.
  rewrite mulrA in hScaled;exact:le_trans hSecond hScaled.
constructor.
- move=>i x hx;exact:(@current_compact_smooth_image R nu omega V W E g Lg Zg b
    hB i (a i x) (@current_compact_smooth_image R n nu U Zg K f Lf Zf a hA i x hx)).
- exact:hSmooth.
- exists (Lg*Lf);split;first exact:mulr_ge0 hLg hLf.
  move=>i x hx.
  have hxZ:Zf x:=@current_compact_smooth_domain_contains R n nu U Zg K f Lf
    Zf a hA x hx.
  have hActual:=@current_map_differential_actual R n omega Zf (composite i)
    (hSmooth i) x hxZ.
  apply:hom_operator_norm_least;first exact:mulr_ge0 hLg hLf.
  exact:(@critical_local_lipschitz_differential_bound R X Z NX NZ hNX hNZ
    Zf Zf (composite i) x (@current_map_differential R n omega Zf (composite i) x)
    (Lg*Lf) hActual
    (@current_compact_smooth_domain_open R n nu U Zg K f Lf Zf a hA x hxZ)
    (hLipschitz i)).
- move=>eps hEps.
  have hDen:0<2*(Lg+1) by nra.
  have hFirstTolerance:0<eps/(2*(Lg+1)) by rewrite divr_gt0.
  have hHalf:0<eps/2 by lra.
  have[N hN]:=current_compact_smooth_uniform hA hFirstTolerance.
  have[M hM]:=current_compact_smooth_uniform hB hHalf.
  exists (maxn N M)=>i hi x hx.
  have hxK:smooth_compact_carrier K x:=hx.
  have hxZ:Zf x:=@current_compact_smooth_domain_contains R n nu U Zg K f Lf
    Zf a hA x hxK.
  have hFX:=hFInE x hxK.
  have hFZ:Zg (f x):=@current_compact_smooth_domain_contains R nu omega
    V W E g Lg Zg b hB (f x) hFX.
  have hAZ:Zg (a i x):=current_compact_smooth_image hA i hxZ.
  have hMapError:=hN i (leq_trans (leq_maxl N M) hi) x hxK.
  have hImageError:=hM i (leq_trans (leq_maxr N M) hi) (f x) hFX.
  have hFirst:NZ (b i (a i x)-b i (f x))<=Lg*NY (a i x-f x):=
    (current_compact_smooth_lipschitz hB i).2 (a i x) (f x) hAZ hFZ.
  have hTriangle:=real_seminorm_triangle hNZ.1
    (b i (a i x)-b i (f x)) (b i (f x)-g (f x)).
  rewrite addrA subrK in hTriangle.
  have hScaled:=ler_wpM2l hLg (ltW hMapError).
  have hBound:=le_trans hTriangle (lerD (le_trans hFirst hScaled) (ltW hImageError)).
  have hCancel:eps/(2*(Lg+1))*(2*(Lg+1))=eps by rewrite divfK // gt_eqF.
  have hPositive:0<eps/(2*(Lg+1)):=hFirstTolerance.
  apply:le_lt_trans hBound _.
  nra.
Qed.
End CurrentNestedSmoothComposite.
