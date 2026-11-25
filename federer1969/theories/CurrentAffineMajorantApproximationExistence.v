(** Federer (1969), 4.1.14, pp. 371–372: construct
    compatible smooth affine approximants from the original
    continuous Lebesgue-AE differential majorant. Smooth both
    endpoints on a compact enlargement of K, restrict to one
    common open source, and take a common tail. Uniform
    approximation on the enlargement preserves the arbitrary
    open target on the entire chosen time-space source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity NormBoundedLinearTopology NormCompactFunctionBound
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockLinearMaps LipschitzUP OpenLocalLipschitzCompact
  SmoothCompactSet CurrentLipschitzCompactImage CurrentHomotopyUP
  CurrentAffineHomotopySealed CurrentAffineHomotopyClass CurrentCompactTimeCylinder
  CurrentSmoothApproximationUP CurrentCompactSmoothApproximationUP
  CurrentCompactMajorantApproximationUP CurrentCompactMajorantApproximationExistence
  CurrentMapDifferential CurrentMapDifferentialOpenRestriction EuclideanHomOperator
  CurrentAffineCompactSourceMargin CurrentCompactSmoothOpenTail
  CurrentAffineFamilyLipschitzBound CurrentAffineSmoothApproximation
  CurrentAffineMajorantApproximationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineMajorantApproximationExistence.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall x,U x->V (g x).
Hypothesis hFLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g.
Variable K:smooth_compact_set hNX U.
Variable sigma:X->R^o.
Hypothesis hSigma:norm_class_zero NX (fun t:R^o=>`|t|) U sigma.
Hypothesis hFMajorant:@is_current_ae_differential_majorant R n nu U f sigma.
Hypothesis hGMajorant:@is_current_ae_differential_majorant R n nu U g sigma.
Hypothesis hBand:forall (t:R) (x:X),0<=t<=1->smooth_compact_carrier K x->
  V ((1-t)*:f x+t*:g x).

(** Source for [current_affine_majorant_approximation_exists]:
    compatible smooth endpoints with the original sigma cap
    and one genuine V-valued affine approximation on an
    original open time-space neighbourhood, Federer 4.1.14,
    pp. 371–372. Every choice is internal to this
    existence proof. No convexity of V, whole-U segment
    condition or variation-AE differential bound is added. *)
Theorem current_affine_majorant_approximation_exists:
  exists A:set R,exists W:set X,exists a b:nat->X->Y,exists eta:nat->R,
    @is_current_affine_majorant_approximation R n nu U V K f g sigma A W a b eta.
Proof.
have hFClass:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U f hU hFLocal.
have hGClass:=@norm_open_local_lipschitz_class_zero R X Y NX NY hNX hNY U g hU hGLocal.
have[A [W [L [d [hA [hWOpen [hKW [hWL [hEmpty [hd [hTime hMargin]]]]]]]]]]]:=
  @current_affine_compact_source_margin R n nu U V hU hV f g hFClass hGClass K hBand.
have hW:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX W x).2
    (open_nbhs_nbhs (conj hWOpen hx)).
have hWU:W `<=` U.
  move=>x hx;exact:smooth_compact_in_domain L x (hWL x hx).
have hKL:smooth_compact_carrier K `<=` smooth_compact_carrier L.
  move=>x hx;exact:hWL x (hKW x hx).
have[ZA [aa [ea hFA]]]:=@current_compact_majorant_smooth_approximation_exists R n nu
  U V hU hV L f sigma hFLocal hFImage hSigma hFMajorant.
have[ZB [bb [eb hGB]]]:=@current_compact_majorant_smooth_approximation_exists R n nu
  U V hU hV L g sigma hGLocal hGImage hSigma hGMajorant.
have[Lf hStrongF]:=current_compact_majorant_ordinary hFA.
have[Lg hStrongG]:=current_compact_majorant_ordinary hGB.
have hWZA:W `<=` ZA.
  move=>x hx;exact:(@current_compact_smooth_domain_contains R n nu U V L f Lf
    ZA aa hStrongF x (hWL x hx)).
have hWZB:W `<=` ZB.
  move=>x hx;exact:(@current_compact_smooth_domain_contains R n nu U V L g Lg
    ZB bb hStrongG x (hWL x hx)).
pose delta:=Num.min 1 (d/8).
have hDelta:0<delta by rewrite /delta lt_min ltr01 divr_gt0 // ltr0n.
have hDeltaOne:delta<=1 by rewrite /delta ge_min lexx.
have hDeltaTarget:delta<=d/8 by rewrite /delta ge_min lexx orbT.
have[NF hNF]:=current_compact_smooth_uniform hStrongF hDelta.
have[NG hNG]:=current_compact_smooth_uniform hStrongG hDelta.
pose N:=maxn NF NG.
pose a (i:nat):X->Y:=aa (N+i)%N.
pose b (i:nat):X->Y:=bb (N+i)%N.
pose eta (i:nat):R:=ea (N+i)%N+eb (N+i)%N.
have hTailA:forall i x,smooth_compact_carrier L x->NY (a i x-f x)<delta.
  move=>i x hx;exact:hNF (N+i)%N
    (leq_trans (leq_maxl NF NG) (leq_addr i N)) x hx.
have hTailB:forall i x,smooth_compact_carrier L x->NY (b i x-g x)<delta.
  move=>i x hx;exact:hNG (N+i)%N
    (leq_trans (leq_maxr NF NG) (leq_addr i N)) x hx.
have hFirst:=@current_compact_smooth_open_tail R n nu U V K L hKL f Lf ZA W
  hW hWZA hKW aa N hStrongF.
have hSecond:=@current_compact_smooth_open_tail R n nu U V K L hKL g Lg ZB W
  hW hWZB hKW bb N hStrongG.
have[MF [hMF hFBound]]:=@norm_class_zero_compact_bounded R X Y NX NY hNX hNY
  U (smooth_compact_carrier L) f (smooth_compact_is_compact L)
  (smooth_compact_in_domain L) hFClass.
have[MG [hMG hGBound]]:=@norm_class_zero_compact_bounded R X Y NX NY hNX hNY
  U (smooth_compact_carrier L) g (smooth_compact_is_compact L)
  (smooth_compact_in_domain L) hGClass.
pose M:=MF+MG+1.
have hM:0<=M by rewrite /M;lra.
have hValuesA:forall i x,W x->NY (a i x)<=M.
  move=>i x hx.
  have hError:=hTailA i x (hWL x hx).
  have hBound:=hFBound x (hWL x hx).
  have hTriangle:=real_seminorm_triangle hNY.1 (a i x-f x) (f x).
  rewrite subrK in hTriangle.
  rewrite /M;lra.
have hValuesB:forall i x,W x->NY (b i x)<=M.
  move=>i x hx.
  have hError:=hTailB i x (hWL x hx).
  have hBound:=hGBound x (hWL x hx).
  have hTriangle:=real_seminorm_triangle hNY.1 (b i x-g x) (g x).
  rewrite subrK in hTriangle.
  rewrite /M;lra.
have hLipA:forall i,@is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) W (a i) Lf.
  move=>i;split;first exact:current_compact_smooth_bound_nonnegative hStrongF.
  move=>x y hx hy.
  exact:(current_compact_smooth_lipschitz hStrongF (N+i)%N).2 x y (hWZA x hx) (hWZA y hy).
have hLipB:forall i,@is_metric_lipschitz_bound R (real_norm_metric_space hNX)
    (real_norm_metric_space hNY) W (b i) Lg.
  move=>i;split;first exact:current_compact_smooth_bound_nonnegative hStrongG.
  move=>x y hx hy.
  exact:(current_compact_smooth_lipschitz hStrongG (N+i)%N).2 x y (hWZB x hx) (hWZB y hy).
pose AU:=@current_homotopy_product_domain R n A W.
pose H:=@CurrentAffineHomotopy.value R n nu f g.
pose Hi (i:nat):=@CurrentAffineHomotopy.value R n nu (a i) (b i).
have hOriginalImage:forall z,AU z->V (H z).
  move=>z [ht hx];rewrite /H current_affine_homotopy_coordinates.
  apply:(@hMargin _ _ _ ht hx).
  by rewrite subrr (real_seminorm_zero hNY.1).
have hImages:forall i z,AU z->V (Hi i z).
  move=>i z [ht hx].
  pose t:=@euclidean_one_project R (@euclidean_first_block_map R 1%N n z).
  pose x:=@euclidean_last_block_map R 1%N n z.
  have hErrorA:=hTailA i x (hWL x hx).
  have hErrorB:=hTailB i x (hWL x hx).
  have[hT hOneT]:=hTime t ht.
  apply:(hMargin t x (Hi i z) ht hx).
  have hDifference:Hi i z-((1-t)*:f x+t*:g x)=
      (1-t)*:(a i x-f x)+t*:(b i x-g x).
    rewrite /Hi current_affine_homotopy_coordinates /t /x !scalerBr.
    by rewrite opprD addrACA.
  rewrite hDifference.
  have hTriangle:=real_seminorm_triangle hNY.1
    ((1-t)*:(a i x-f x)) (t*:(b i x-g x)).
  rewrite !(real_seminorm_scale hNY.1) in hTriangle.
  have hFirstBound:=ler_wpM2r (real_seminorm_nonnegative hNY.1 (a i x-f x)) hOneT.
  have hSecondBound:=ler_wpM2r (real_seminorm_nonnegative hNY.1 (b i x-g x)) hT.
  have hBound:=le_trans hTriangle (lerD hFirstBound hSecondBound).
  apply:le_lt_trans hBound _.
  nra.
have[C hLipschitz]:=@current_affine_family_lipschitz_bound R n nu A W hTime
  a b Lf Lg M hM hLipA hLipB hValuesA hValuesB.
have hHomotopyApprox:=@current_affine_smooth_approximation R n nu A W V hA hW
  (@current_compact_index_in_open R n U W K hKW) f g a b hFirst hSecond
  hImages C hLipschitz.
exists A,W,a,b,eta.
refine (@Build_is_current_affine_majorant_approximation R n nu U V K f g sigma
  A W a b eta hA hW hKW hWU hEmpty hOriginalImage hFirst hSecond
  _ _ _ _ hHomotopyApprox).
- move=>i;exact:addr_gt0 (current_compact_majorant_error_positive hFA (N+i)%N)
    (current_compact_majorant_error_positive hGB (N+i)%N).
- move=>eps hEps.
  have hHalf:0<eps/2 by lra.
  have[J hJ]:=current_compact_majorant_error_zero hFA hHalf.
  have[Q hQ]:=current_compact_majorant_error_zero hGB hHalf.
  exists (maxn J Q)=>i hi.
  have hOne:=hJ (N+i)%N (leq_trans (leq_trans (leq_maxl J Q) hi) (leq_addl N i)).
  have hTwo:=hQ (N+i)%N (leq_trans (leq_trans (leq_maxr J Q) hi) (leq_addl N i)).
  rewrite /eta;lra.
- move=>i x hx.
  rewrite (@current_map_differential_open_restriction R n nu W ZA hW hWZA
    (aa (N+i)%N) (current_compact_smooth_class hStrongF (N+i)%N) x (hKW x hx)).
  have hCap:=@current_compact_majorant_differential_bound R n nu U V L f sigma
    ZA aa ea hFA (N+i)%N x (hKL x hx).
  have hPositive:=current_compact_majorant_error_positive hGB (N+i)%N.
  rewrite /eta;lra.
- move=>i x hx.
  rewrite (@current_map_differential_open_restriction R n nu W ZB hW hWZB
    (bb (N+i)%N) (current_compact_smooth_class hStrongG (N+i)%N) x (hKW x hx)).
  have hCap:=@current_compact_majorant_differential_bound R n nu U V L g sigma
    ZB bb eb hGB (N+i)%N x (hKL x hx).
  have hPositive:=current_compact_majorant_error_positive hFA (N+i)%N.
  rewrite /eta;lra.
Qed.
End CurrentAffineMajorantApproximationExistence.
