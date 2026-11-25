(** Federer (1969), 3.4.6, p. 324: the original
    coefficient recursion produces homogeneous polynomials of
    exactly the transverse degree j. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import HomogeneousPolynomialFunctions
  WeierstrassCoefficientRecursion WeierstrassHomogeneousArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Recursion.
Variable R:realType.
Variable K:lmodType R.
Variables phi psi q:nat->nat->K->R.
Variable k:nat.
Hypothesis hPhi:forall i j,@is_homogeneous_polynomial R K R^o j (phi i j).
Hypothesis hPsi:forall i j,@is_homogeneous_polynomial R K R^o j (psi i j).
Hypothesis hQ:forall i j,q i j=weierstrass_coefficient_step k phi psi i j q.

(** Source for [weierstrass_recursion_homogeneous]: each
    Q_(i,j) is a homogeneous polynomial of degree j,
    as asserted by the recursion in 3.4.6, p. 324.
    Only smaller-weight polynomials enter either finite sum. *)
Theorem weierstrass_recursion_homogeneous i j:
  @is_homogeneous_polynomial R K R^o j (q i j).
Proof.
have hAll:forall r i j,weierstrass_coefficient_weight k i j=r ->
    @is_homogeneous_polynomial R K R^o j (q i j).
  move=>r;elim/ltn_ind:r=>r ih i0 j0 hRank.
  have hBefore p s:(weierstrass_coefficient_weight k p s<r)%N ->
      @is_homogeneous_polynomial R K R^o s (q p s).
    move=>hps;exact:(ih (weierstrass_coefficient_weight k p s) hps p s (erefl _)).
  have hPrefix:@is_homogeneous_polynomial R K R^o j0
      (fun z=>\sum_(mu<i0) q mu j0 z*phi (i0+k-mu)%N 0%N z).
    apply:(@weierstrass_homogeneous_sum R K j0 (Finite.clone 'I_i0 _)).
    move=>mu.
    have hWeight:(weierstrass_coefficient_weight k mu j0<r)%N.
      rewrite -hRank;exact:weierstrass_prefix_weight_smaller (ltn_ord mu).
    have hProduct:=@weierstrass_homogeneous_multiply R K j0 0%N
      (q mu j0) (phi (i0+k-mu)%N 0%N) (hBefore mu j0 hWeight) (hPhi (i0+k-mu)%N 0%N).
    by rewrite addn0 in hProduct.
  have hCross:@is_homogeneous_polynomial R K R^o j0
      (fun z=>\sum_(mu<(i0+k).+1) \sum_(nu<j0)
        q mu nu z*phi (i0+k-mu)%N (j0-nu)%N z).
    apply:(@weierstrass_homogeneous_sum R K j0 (Finite.clone 'I_(i0+k).+1 _)).
    move=>mu.
    apply:(@weierstrass_homogeneous_sum R K j0 (Finite.clone 'I_j0 _)).
    move=>nu.
    have hMu:(mu<=i0+k)%N by have:=ltn_ord mu;rewrite ltnS.
    have hNu:(nu<=j0)%N:=ltnW (ltn_ord nu).
    have hWeight:(weierstrass_coefficient_weight k mu nu<r)%N.
      rewrite -hRank;exact:weierstrass_cross_weight_smaller hMu (ltn_ord nu).
    have hProduct:=@weierstrass_homogeneous_multiply R K nu (j0-nu)%N
      (q mu nu) (phi (i0+k-mu)%N (j0-nu)%N) (hBefore mu nu hWeight)
      (hPhi (i0+k-mu)%N (j0-nu)%N).
    by rewrite subnKC // in hProduct.
  rewrite (hQ i0 j0) /weierstrass_coefficient_step.
  apply:weierstrass_homogeneous_add;last exact:weierstrass_homogeneous_negate hCross.
  apply:weierstrass_homogeneous_add;first exact:hPsi (i0+k)%N j0.
  exact:weierstrass_homogeneous_negate hPrefix.
exact:(hAll (weierstrass_coefficient_weight k i j) i j (erefl _)).
Qed.
End Recursion.
