(** Federer (1969), 4.1.15, p. 372: choose the
    two genuine smoothing families with radii tending to zero.
    One family smooths f; the other smooths its original
    radius-dependent G_r. Both have uniform Lipschitz bounds,
    and each pair agrees near every original coincidence set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology ring lra.
From Federer Require Import RealNormUP NormMetric NormRegularity NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP MetricOpenThickening GeometricUniformTail
  SmoothingKernelSealed SmoothingDilationSealed SmoothingConvolutionUP
  RadialAgreementMapSealed RadialAgreementMapBounds RadialAgreementMapLipschitz
  RadialAgreementNeighbourhood RadialSmoothingAgreement AmbientLipschitzSmoothingFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RadialSmoothingFamilies.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation MX:=(real_norm_metric_space hNX).
Local Notation MY:=(real_norm_metric_space hNY).
Variables F G:X->Y.
Variables Lf Lg:R.
Hypotheses (hLf:0<=Lf) (hLg:0<=Lg).
Hypothesis hFBound:forall x y,NY (F x-F y)<=Lf*NX (x-y).
Hypothesis hGBound:forall x y,NY (G x-G y)<=Lg*NX (x-y).

(** Source for [radial_smoothing_families_exists]: the
    actual simultaneous approximations on p. 372 of
    Federer 4.1.15, before restricting to the original
    open target. No original target-image condition is
    imposed on the ambient G_r. The maps may take
    values outside that target away from the eventual source. *)
Theorem radial_smoothing_families_exists:
  exists a:nat->X->Y,exists b:nat->X->Y,
    (forall i,norm_class_all_orders hNX hNY setT (a i)) /\
    (forall i,norm_class_all_orders hNX hNY setT (b i)) /\
    (forall i x y,NY (a i x-a i y)<=Lf*NX (x-y)) /\
    (forall i x y,NY (b i x-b i y)<=(2*Lf+Lg)*NX (x-y)) /\
    (forall delta:R,0<delta->exists N:nat,forall i:nat,(N<=i)%N->
      forall x,NY (a i x-F x)<delta) /\
    (forall delta:R,0<delta->exists N:nat,forall i:nat,(N<=i)%N->
      forall x,NY (b i x-G x)<delta) /\
    forall A:set X,(forall x,A x->F x=G x)->
      forall i,exists W:set X,@open MX W /\ A `<=` W /\
        forall x,W x->a i x=b i x.
Proof.
pose q:R:=1/2.
have hq:0<q<1 by rewrite /q;apply/andP;split;lra.
pose D:=Lf+Lg.
pose B:=4*(D+1).
pose C:=2*Lf+Lg.
have hD:0<=D:=addr_ge0 hLf hLg.
have hC:0<=C:=addr_ge0 (mulr_ge0 (ler0n R 2) hLf) hLg.
have hB:0<B by rewrite /B;lra.
pose r (i:nat):R:=q^+i.
have hR:forall i,0<r i.
  move=>i;rewrite /r.
  exact:(exprn_gt0 i ((andP hq).1)).
pose epsilon (i:nat):R:=r i/B.
have hEpsilon:forall i,0<epsilon i.
  move=>i;exact:divr_gt0 (@hR i) hB.
have hSmall:forall i,2*(Lf+Lg)*epsilon i<r i.
  move=>i.
  have hProduct:B*epsilon i=r i by rewrite /epsilon mulrC divfK ?gt_eqF.
  have h24:(2:R)<=4 by rewrite ler_nat.
  have hFour:(0:R)<4 by rewrite ltr0n.
  have hExpand:B = 4*D+4 by rewrite /B;ring.
  have hFactor:2*(Lf+Lg)<B.
    change (is_true (2*D<B)).
    apply:(le_lt_trans (ler_wpM2r hD h24)).
    by rewrite hExpand ltrDl.
  rewrite -hProduct (ltr_pM2r (@hEpsilon i));exact:hFactor.
pose H i:=@RadialAgreementMap.value R n nu (r i) (@hR i) F G.
pose hH i:=@RadialAgreementMap.laws R n nu (r i) (@hR i) F G.
have hFM:@is_metric_lipschitz_bound R MX MY setT F Lf.
  split;first exact:hLf.
  move=>x y _ _;exact:(@hFBound x y).
have hGM:@is_metric_lipschitz_bound R MX MY setT G Lg.
  split;first exact:hLg.
  move=>x y _ _;exact:(@hGBound x y).
have hHBound:forall i x y,NY (H i x-H i y)<=C*NX (x-y).
  move=>i x y.
  have hMetric:=@radial_agreement_lipschitz_bound R n nu (r i) (@hR i)
    F G (H i) (hH i) setT Lf Lg hFM hGM.
  exact:hMetric.2 x y Logic.I Logic.I.
have[a [hAConvolution [hAClass [hALip hAError]]]]:=
  @ambient_lipschitz_smoothing_family_exists R n nu (fun _:nat=>F)
    Lf hLf (fun _=>hFBound) epsilon hEpsilon.
have[b [hBConvolution [hBClass [hBLip hBError]]]]:=
  @ambient_lipschitz_smoothing_family_exists R n nu H C hC hHBound epsilon hEpsilon.
have hAUniform:forall delta:R,0<delta->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,NY (a i x-F x)<delta.
  move=>delta hDelta.
  have hM:0<=Lf/B:=divr_ge0 hLf (ltW hB).
  have[N hN]:=@geometric_uniform_tail R q (Lf/B) delta hq hM hDelta.
  exists N=>i hi x.
  have hScale:Lf*epsilon i=q^+i*(Lf/B) by rewrite /epsilon /r;ring.
  have hEstimate:=hAError i x.
  rewrite hScale in hEstimate.
  exact:(le_lt_trans hEstimate (hN i hi)).
have hBUniform:forall delta:R,0<delta->exists N:nat,forall i:nat,(N<=i)%N->
    forall x,NY (b i x-G x)<delta.
  move=>delta hDelta.
  have hM:0<=C/B+1:=addr_ge0 (divr_ge0 hC (ltW hB)) ler01.
  have[N hN]:=@geometric_uniform_tail R q (C/B+1) delta hq hM hDelta.
  exists N=>i hi x.
  have hTriangle:=real_seminorm_triangle hNY.1 (b i x-H i x) (H i x-G x).
  have hSplit:(b i x-H i x)+(H i x-G x)=b i x-G x by rewrite addrA subrK.
  rewrite hSplit in hTriangle.
  have hDisplacement:=@radial_agreement_displacement R n nu (r i) (@hR i)
    F G (H i) (hH i) x.
  have hBound:=le_trans hTriangle (lerD (hBError i x) hDisplacement).
  have hScale:C*epsilon i+r i=q^+i*(C/B+1) by rewrite /epsilon /r;ring.
  rewrite hScale in hBound.
  exact:(le_lt_trans hBound (hN i hi)).
exists a,b;split;first exact:hAClass.
split;first exact:hBClass.
split;first exact:hALip.
split;first exact:hBLip.
split;first exact:hAUniform.
split;first exact:hBUniform.
move=>A hAgreement i.
pose W:=@metric_open_thickening R MX A (epsilon i).
exists W;split;first exact:metric_open_thickening_open.
split;first exact:(@metric_open_thickening_includes R MX A (epsilon i) (@hEpsilon i)).
move=>x hx.
pose phi:=@SmoothingKernel.value R n.
pose hPhi:=@SmoothingKernel.laws R n.
pose family:=@SmoothingDilation.value R n phi.
pose hFamily:=@SmoothingDilation.laws R n phi.
apply:(@radial_smoothing_agreement R n nu setT F G (H i) (r i) (@hR i)
  (hH i) phi family (epsilon i) (a i) (b i) hPhi hFamily (@hEpsilon i)
  (hAConvolution i) (hBConvolution i) x).
split;first exact:Logic.I.
exact:(@radial_agreement_neighbourhood_ball R n nu F G A Lf Lg hFM hGM
  hAgreement (r i) (epsilon i) (@hEpsilon i) (@hSmall i) x hx).
Qed.
End RadialSmoothingFamilies.
