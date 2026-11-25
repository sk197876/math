(** Federer (1969), 3.4.6(2), p. 322: division
    of the original monic coordinate power proves Q(0)
    nonzero and every transverse constant coefficient zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP AnalyticGermUP AnalyticGermRing WeierstrassRegularUP
  WeierstrassRegularCoefficients WeierstrassDivisionUP WeierstrassCoefficientUP
  WeierstrassCoefficientExistence WeierstrassCoefficientProduct WeierstrassCoefficientDifference
  WeierstrassPolynomialHighCoefficients WeierstrassAxisProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [weierstrass_preparation_coefficient_values]:
    the actual low remainder axis coefficients vanish,
    and the actual quotient value is nonzero, as required
    in 3.4.6(2), p. 322. These conclusions
    follow from the original division equation and regularity;
    neither is an extra hypothesis. *)
Theorem weierstrass_preparation_coefficient_values (R:realType) (X K:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (v:X) (inclusion:Hom K X) k
    (Phi Psi Q T:@analytic_germ_ring R X NX hNX 0)
    (phi psi q r:nat->nat->K->R):
  is_weierstrass_regular_germ Phi k v ->
  @is_weierstrass_division R X NX hNX k v Phi Psi Q T ->
  (forall i j,is_weierstrass_split_coefficient Phi v inclusion i j (phi i j)) ->
  (forall i j,is_weierstrass_split_coefficient Psi v inclusion i j (psi i j)) ->
  (forall i j,is_weierstrass_split_coefficient Q v inclusion i j (q i j)) ->
  (forall i j,is_weierstrass_split_coefficient T v inclusion i j (r i j)) ->
  (forall i j z,psi i j z=if ((i==k)&&(j==0))%N then 1 else 0) ->
  (forall i,(i<k)%N ->forall z,r i 0%N z=0) /\forall z,q 0%N 0%N z<>0.
Proof.
move=>hRegular hDivision hPhi hPsi hQ hR hMonic.
pose M:@analytic_germ_ring R X NX hNX 0:=Phi*Q.
have [p hP]:=@weierstrass_split_coefficients_exist R X K NX hNX M v inclusion.
have hLow:=@weierstrass_regular_low_coefficients R X K NX hNX Phi k v inclusion phi hRegular hPhi.
have hHigh:=@weierstrass_polynomial_high_coefficients R X K NX hNX k v inclusion T r
  (weierstrass_division_polynomial_remainder hDivision) hR.
have hRemainder:T=Psi-M.
  by rewrite /M (weierstrass_division_identity hDivision) [Phi*Q]mulrC addrAC subrr add0r.
have hProduct:=@weierstrass_split_coefficient_product R X K NX hNX Phi Q v inclusion phi q p hPhi hQ hP.
have hAxis i z:p i 0%N z=\sum_(mu<i.+1) phi (i-mu)%N 0%N z*q mu 0%N z.
  rewrite hProduct;apply:eq_bigr=>mu _;by rewrite big_ord1 /= subn0.
have hDifference i z:r i 0%N z=psi i 0%N z-p i 0%N z.
  have hActual:is_weierstrass_split_coefficient (Psi-M) v inclusion i 0%N (r i 0%N).
    by rewrite -hRemainder.
  exact:(@weierstrass_split_coefficient_difference R X K NX hNX Psi M v inclusion
    i 0%N (psi i 0%N) (p i 0%N) (r i 0%N) (hPsi _ _) (hP _ _) hActual z).
split.
- move=>i hi z.
  have hNe:(i!=k)%N by apply/eqP=>h;by rewrite h ltnn in hi.
  rewrite hDifference hMonic (negbTE hNe) /= hAxis.
  rewrite (@weierstrass_axis_product_below R k (fun n=>phi n 0%N z) (fun n=>q n 0%N z)
    (fun n hn=>hLow n hn z) i hi) subrr.
  reflexivity.
- move=>z hZero.
  have hLeading:=hDifference k z.
  rewrite (hHigh k (leqnn k) 0%N z) hMonic !eqxx /= hAxis
    (@weierstrass_axis_product_leading R k (fun n=>phi n 0%N z) (fun n=>q n 0%N z)
      (fun n hn=>hLow n hn z)) hZero mulr0 subr0 in hLeading.
  have hNot:(1:R)!=0:=oner_neq0 R.
  by rewrite -hLeading eqxx in hNot.
Qed.
