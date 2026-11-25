(** Federer (1969), 3.4.6, p. 324: actual recursively
    defined quotient coefficients satisfy the original geometric
    bound, by induction on i+(k+1)j. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import WeierstrassCoefficientRecursion WeierstrassNumericalMajorant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Bounds.
Variable R:realType.
Variable K:Type.
Variable P:K->Prop.
Variables phi psi q:nat->nat->K->R.
Variables b c alpha beta gamma:R.
Variable k:nat.
Hypotheses (hb:0<b) (hc:0<c) (hAlpha:0<alpha) (hBeta:c<beta) (hGamma:c<gamma).
Hypothesis hDelta:b*c^+k/alpha+b*c^+k.+1/(beta-c)+
  b*c*beta^+k.+1/((beta-c)*(gamma-c))<1.
Hypothesis hPhi:forall i j z,P z ->`|phi i j z|<=b*c^+(i+j).
Hypothesis hPsi:forall i j z,P z ->`|psi i j z|<=b*c^+(i+j).
Hypothesis hQ:forall i j,q i j=weierstrass_coefficient_step k phi psi i j q.

(** Source for [weierstrass_coefficient_bound]: the original
    coefficient bound |Q_(i,j)(z)|<=alpha beta^i gamma^j
    on the closed transverse unit ball, 3.4.6, p. 324.
    The set P may be that ball or any set carrying
    the original input bounds. No quotient bound is assumed. *)
Theorem weierstrass_coefficient_bound i j z:
  P z ->`|q i j z|<=alpha*beta^+i*gamma^+j.
Proof.
move=>hz.
have hAll:forall r i j,weierstrass_coefficient_weight k i j=r ->
    `|q i j z|<=alpha*beta^+i*gamma^+j.
  move=>r;elim/ltn_ind:r=>r ih i0 j0 hRank.
  have hBefore p s:(weierstrass_coefficient_weight k p s<r)%N ->
      `|q p s z|<=alpha*beta^+p*gamma^+s.
    move=>hps;exact:(ih (weierstrass_coefficient_weight k p s) hps p s (erefl _)).
  have hPrefix:`|\sum_(mu<i0) q mu j0 z*phi (i0+k-mu)%N 0%N z|<=
      \sum_(mu<i0) alpha*beta^+mu*gamma^+j0*b*c^+(i0+k-mu).
    apply:le_trans (ler_norm_sum _ _ _) _;apply:ler_sum=>mu _.
    rewrite normrM.
    have hWeight:(weierstrass_coefficient_weight k mu j0<r)%N.
      rewrite -hRank;exact:weierstrass_prefix_weight_smaller (ltn_ord mu).
    have hFirst:=hBefore mu j0 hWeight.
    have hSecond:=@hPhi (i0+k-mu)%N 0%N z hz.
    rewrite addn0 in hSecond.
    have hCoefficient:0<=alpha*beta^+mu*gamma^+j0.
      exact:mulr_ge0 (mulr_ge0 (ltW hAlpha) (exprn_ge0 mu (ltW (lt_trans hc hBeta))))
        (exprn_ge0 j0 (ltW (lt_trans hc hGamma))).
    have hBound:=le_trans (ler_wpM2r (normr_ge0 _) hFirst)
      (ler_wpM2l hCoefficient hSecond).
    by rewrite mulrA in hBound.
  have hCross:`|\sum_(mu<(i0+k).+1) \sum_(nu<j0)
      q mu nu z*phi (i0+k-mu)%N (j0-nu)%N z|<=
      \sum_(mu<(i0+k).+1) \sum_(nu<j0)
        alpha*beta^+mu*gamma^+nu*b*c^+(i0+k-mu+j0-nu).
    apply:le_trans (ler_norm_sum _ _ _) _;apply:ler_sum=>mu _.
    apply:le_trans (ler_norm_sum _ _ _) _;apply:ler_sum=>nu _.
    rewrite normrM.
    have hMu:(mu<=i0+k)%N by have:=ltn_ord mu;rewrite ltnS.
    have hNu:(nu<=j0)%N:=ltnW (ltn_ord nu).
    have hWeight:(weierstrass_coefficient_weight k mu nu<r)%N.
      rewrite -hRank;exact:weierstrass_cross_weight_smaller hMu (ltn_ord nu).
    have hFirst:=hBefore mu nu hWeight.
    have hSecond:=@hPhi (i0+k-mu)%N (j0-nu)%N z hz.
    rewrite addnBA // in hSecond.
    have hCoefficient:0<=alpha*beta^+mu*gamma^+nu.
      exact:mulr_ge0 (mulr_ge0 (ltW hAlpha) (exprn_ge0 mu (ltW (lt_trans hc hBeta))))
        (exprn_ge0 nu (ltW (lt_trans hc hGamma))).
    have hBound:=le_trans (ler_wpM2r (normr_ge0 _) hFirst)
      (ler_wpM2l hCoefficient hSecond).
    by rewrite mulrA in hBound.
  rewrite (hQ i0 j0) /weierstrass_coefficient_step.
  apply:le_trans (ler_normB _ _) _.
  apply:le_trans (lerD (ler_normB _ _) (lexx _)) _.
  have hOriginal:=@hPsi (i0+k)%N j0 z hz.
  have hDegree:(i0+k+j0)%N=(i0+j0+k)%N by rewrite addnAC.
  rewrite hDegree in hOriginal.
  apply:le_trans (lerD (lerD hOriginal hPrefix) hCross) _.
  exact:ltW (@weierstrass_numerical_majorant R b c alpha beta gamma k i0 j0
    hb hc hAlpha hBeta hGamma hDelta).
exact:(hAll (weierstrass_coefficient_weight k i j) i j (erefl _)).
Qed.
End Bounds.
