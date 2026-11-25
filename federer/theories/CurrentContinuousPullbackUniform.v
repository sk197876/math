(** Federer (1969), 4.1.14, p. 372: the final
    class-one identity permits every continuous target form.
    Use the preceding multilinear increment estimate and
    compact-nearby uniform continuity on the original image
    f(K). No smoothness, compact support or global bound
    of the continuous form is needed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassZeroComposition NormClassHigherRestriction
  NormCompactFunctionBound CompactNearbyUniformContinuity SmoothCompactSet
  SmoothCompactImage InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanHomOperator AlternatingForms AlternatingDual
  CurrentCoefficientNorms CurrentFormPullbackDifferenceBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentContinuousPullbackUniform.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation PN := (@current_form_comass R h2 n m).
Local Notation QN := (@current_form_comass R h2 nu m).
Local Notation hQN := (@current_form_comass_real_norm R h2 nu m).
Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation hOp := (@euclidean_operator_norm_is_norm R n nu).
Local Notation pull F := (@A_m_dual R X Y R^o (hom_as_linear F) m).
Variables (U:set X) (V:set Y) (f:X->Y) (D:X->Hom X Y).
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_zero NX NY U f.
Arguments hf : clear implicits.
Hypothesis hD:norm_class_zero NX Op U D.
Arguments hD : clear implicits.
Variable phi:Y->A_m Y R^o m.
Hypothesis hPhi:norm_class_zero NY QN V phi.
Arguments hPhi : clear implicits.

(** Source for [current_continuous_pullback_class]: a
    continuous form pulled back by an original class-one
    map is continuous, as needed to evaluate both sides
    of Federer 4.1.14, p. 372. This supporting
    field version isolates the two original continuity laws;
    the existing class-one differential theorem supplies D. *)
Theorem current_continuous_pullback_class:
  norm_class_zero NX PN U (fun x=>pull (D x) (phi (f x))).
Proof.
have hComposite:=@norm_class_zero_composition R X Y (A_m Y R^o m)
  NX NY QN U V f phi hf hPhi.
have hInclusion:forall x,U x->U x /\V (f x).
  move=>x hx;split;first exact:hx.
  exact:hImage x hx.
have hCoefficient:norm_class_zero NX QN U (fun x=>phi (f x)).
  move=>a ha;split;first exact:(hf a ha).1.
  move=>epsilon hEpsilon.
  have[d [hd hBound]]:=(hComposite a (hInclusion a ha)).2 epsilon hEpsilon.
  exists d;split;first exact:hd.
  move=>h hAh hSmall.
  exact:hBound h (hInclusion (a+h) hAh) hSmall.
move=>a ha;split;first exact:(hf a ha).1.
move=>epsilon hEpsilon.
pose c:=Op (D a)+1.
pose b:=QN (phi (f a)).
have hOpNonnegative:=real_seminorm_nonnegative hOp.1 (D a).
have hc:1<=c by rewrite /c;lra.
have hC:0<=c:=le_trans ler01 hc.
have hb:0<=b:=real_seminorm_nonnegative hQN.1 (phi (f a)).
pose A:=c^+m+m%:R*(b*c^+m).
have hPower:0<=c^+m:=exprn_ge0 m hC.
have hA:0<=A.
  apply:addr_ge0;first exact:hPower.
  exact:mulr_ge0 (ler0n _ _) (mulr_ge0 hb hPower).
have hDen:0<A+1 by lra.
pose tolerance:=epsilon/(A+1).
have hTolerance:0<tolerance by rewrite /tolerance divr_gt0.
have[dc [hdc hCoefficientBound]]:=(hCoefficient a ha).2 tolerance hTolerance.
have[dd [hdd hDifferentialBound]]:=(hD a ha).2 tolerance hTolerance.
have[db [hdb hCapBound]]:=(hD a ha).2 1 ltr01.
exists (Num.min dc (Num.min dd db));split.
- by rewrite !lt_min hdc hdd hdb.
- move=>h hAh hSmall.
  have /andP [hSmallC /andP [hSmallD hSmallB]]:
      (NX h<dc)&&((NX h<dd)&&(NX h<db)) by rewrite -!lt_min.
  have hCap:Op (D (a+h))<=c.
    have hTriangle:=real_seminorm_triangle hOp.1 (D (a+h)-D a) (D a).
    rewrite subrK in hTriangle.
    have hCapSmall:=hCapBound h hAh hSmallB.
    rewrite /c;lra.
  have hOriginal:Op (D a)<=c by rewrite /c;lra.
  have hDifferential:Op (D (a+h)-D a)<=tolerance:=
    ltW (hDifferentialBound h hAh hSmallD).
  have hCoefficientError:QN (phi (f (a+h))-phi (f a))<=tolerance:=
    ltW (hCoefficientBound h hAh hSmallC).
  have hBound:=@current_form_pullback_difference_bound R h2 n nu m
    (D (a+h)) (D a) c tolerance (phi (f (a+h))) (phi (f a))
    hc (ltW hTolerance) hCap hOriginal hDifferential.
  have hTotal:PN (pull (D (a+h)) (phi (f (a+h)))-
      pull (D a) (phi (f a)))<=tolerance*A.
    apply:le_trans hBound _.
    have hFirst:=ler_wpM2r hPower hCoefficientError.
    have hSecond:=lexx (m%:R*(b*(tolerance*c^+m))).
    have hSum:=lerD hFirst hSecond.
    have hAlgebra:tolerance*c^+m+m%:R*(b*(tolerance*c^+m))=tolerance*A.
      rewrite /A;ring.
    by rewrite hAlgebra in hSum.
  apply:le_lt_trans hTotal _.
  have hStrict:tolerance*A<tolerance*(A+1) by rewrite ltr_pM2l // ltrDl.
  by rewrite /tolerance divfK ?gt_eqF // in hStrict.
Qed.

Variable K:smooth_compact_set hNX U.
Variables (g:nat->X->Y) (G:nat->X->Hom X Y).
Hypothesis hGImage:forall k x,smooth_compact_carrier K x->V (g k x).
Arguments hGImage : clear implicits.
Hypothesis hUniformValue:forall epsilon:R,0<epsilon->exists k,forall L,
  (k<=L)%N->forall x,smooth_compact_carrier K x->NY (g L x-f x)<epsilon.
Arguments hUniformValue : clear implicits.
Hypothesis hUniformDifferential:forall epsilon:R,0<epsilon->exists k,forall L,
  (k<=L)%N->forall x,smooth_compact_carrier K x->Op (G L x-D x)<epsilon.
Arguments hUniformDifferential : clear implicits.

(** Source for [current_continuous_pullback_uniform_on_compact]:
    uniform convergence of original map values and first
    differentials on K gives uniform convergence of the
    pullbacks of every original continuous form, supporting
    Federer 4.1.14, p. 372. Values outside K
    have no convergence or target-image premise. Degree zero,
    empty K and zero-dimensional spaces are retained. *)
Theorem current_continuous_pullback_uniform_on_compact:
  forall epsilon:R,0<epsilon->exists k,forall L,(k<=L)%N->forall x,
    smooth_compact_carrier K x->
    PN (pull (G L x) (phi (g L x))-pull (D x) (phi (f x)))<epsilon.
Proof.
have[C [hCPositive hCBound]]:=@norm_class_zero_compact_bounded R X (Hom X Y)
  NX Op hNX hOp U (smooth_compact_carrier K) D (smooth_compact_is_compact K)
  (smooth_compact_in_domain K) hD.
pose image:=@smooth_compact_image R X Y NX NY hNX hNY U V f hImage hf K.
have[b [hBPositive hBBound]]:=@norm_class_zero_compact_bounded R Y (A_m Y R^o m)
  NY QN hNY hQN V (smooth_compact_carrier image) phi
  (smooth_compact_is_compact image) (smooth_compact_in_domain image) hPhi.
pose c:=C+1.
have hc:1<=c by rewrite /c;lra.
have hC:0<=c:=le_trans ler01 hc.
have hb:0<=b:=ltW hBPositive.
pose A:=c^+m+m%:R*(b*c^+m).
have hPower:0<=c^+m:=exprn_ge0 m hC.
have hA:0<=A.
  apply:addr_ge0;first exact:hPower.
  exact:mulr_ge0 (ler0n _ _) (mulr_ge0 hb hPower).
move=>epsilon hEpsilon.
have hDen:0<A+1 by lra.
pose tolerance:=epsilon/(A+1).
have hTolerance:0<tolerance by rewrite /tolerance divr_gt0.
have[d [hd hCoefficientBound]]:=@norm_class_zero_compact_uniform_nearby R Y
  (A_m Y R^o m) NY QN hNY hQN V (smooth_compact_carrier image) phi
  (smooth_compact_is_compact image) (smooth_compact_in_domain image) hPhi
  tolerance hTolerance.
have[kCap hCapNear]:=hUniformDifferential 1 ltr01.
have[kValue hValueNear]:=hUniformValue d hd.
have[kDifference hDifferenceNear]:=hUniformDifferential tolerance hTolerance.
exists (maxn kCap (maxn kValue kDifference))=>L hL x hx.
have hLCap:(kCap<=L)%N:=leq_trans (leq_maxl _ _) hL.
have hLRest:(maxn kValue kDifference<=L)%N:=leq_trans (leq_maxr _ _) hL.
have hLValue:(kValue<=L)%N:=leq_trans (leq_maxl _ _) hLRest.
have hLDifference:(kDifference<=L)%N:=leq_trans (leq_maxr _ _) hLRest.
have hOriginal:Op (D x)<=c.
  have hBound:=hCBound x hx;rewrite /c;lra.
have hCap:Op (G L x)<=c.
  have hTriangle:=real_seminorm_triangle hOp.1 (G L x-D x) (D x).
  rewrite subrK in hTriangle.
  have hSmall:=hCapNear L hLCap x hx.
  have hBound:=hCBound x hx;rewrite /c;lra.
have hImageX:smooth_compact_carrier image (f x) by exists x.
have hCoefficientError:QN (phi (g L x)-phi (f x))<=tolerance.
  exact:ltW (hCoefficientBound (f x) (g L x) hImageX (hGImage L x hx)
    (hValueNear L hLValue x hx)).
have hDifference:Op (G L x-D x)<=tolerance:=
  ltW (hDifferenceNear L hLDifference x hx).
have hBound:=@current_form_pullback_difference_bound R h2 n nu m
  (G L x) (D x) c tolerance (phi (g L x)) (phi (f x))
  hc (ltW hTolerance) hCap hOriginal hDifference.
have hTotal:PN (pull (G L x) (phi (g L x))-
    pull (D x) (phi (f x)))<=tolerance*A.
  apply:le_trans hBound _.
  have hFirst:=ler_wpM2r hPower hCoefficientError.
  have hDegree:0<=(m%:R:R) by rewrite ler0n.
  have hSecond:m%:R*(QN (phi (f x))*(tolerance*c^+m))<=
      m%:R*(b*(tolerance*c^+m)).
    exact:(ler_wpM2l hDegree
      (ler_wpM2r (mulr_ge0 (ltW hTolerance) hPower) (hBBound (f x) hImageX))).
  have hSum:=lerD hFirst hSecond.
  have hAlgebra:tolerance*c^+m+m%:R*(b*(tolerance*c^+m))=tolerance*A.
    rewrite /A;ring.
  by rewrite hAlgebra in hSum.
apply:le_lt_trans hTotal _.
have hStrict:tolerance*A<tolerance*(A+1) by rewrite ltr_pM2l // ltrDl.
by rewrite /tolerance divfK ?gt_eqF // in hStrict.
Qed.
End CurrentContinuousPullbackUniform.
