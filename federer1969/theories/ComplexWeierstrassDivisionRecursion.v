(** Federer (1969), 3.4.12, p. 339, extending 3.4.6(1), pp. 322–324:
    every original normalized division candidate satisfies
    the printed quotient coefficient recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ScalarRestriction ComplexScalarSealed ComplexNormUP HolomorphicGermUP
  HolomorphicGermSealed HolomorphicGermRing ComplexWeierstrassDivisionUP ComplexWeierstrassCoefficientUP
  ComplexWeierstrassCoefficientExistence ComplexWeierstrassCoefficientProduct ComplexWeierstrassCoefficientDifference
  WeierstrassRingRecursion WeierstrassRingConvolution ComplexWeierstrassPolynomialHighCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_division_candidate_recursion]:
    the original division equation and neighbourhood derivative
    condition force the exact finite recurrence, proving the
    uniqueness mechanism of 3.4.6(1), pp. 322–324.
    No coefficient identity is an extra hypothesis of
    the numbered existence or uniqueness theorem. *)
Theorem complex_weierstrass_division_candidate_recursion (R:realType) (X K:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:is_complex_norm NX) (v:X) (inclusion:Hom K X) k
    (Phi Psi Q T:@holomorphic_germ_ring R X NX (complex_norm_real hNX) 0) (phi psi q:nat->nat->K->ComplexScalars.C R):
  (forall i j,is_complex_weierstrass_split_coefficient hNX Phi v inclusion i j (phi i j)) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX Psi v inclusion i j (psi i j)) ->
  (forall i j,is_complex_weierstrass_split_coefficient hNX Q v inclusion i j (q i j)) ->
  (forall i,(i<k)%N ->forall z,phi i 0%N z=0) ->(forall z,phi k 0%N z= 1) ->
  @is_complex_weierstrass_division R X NX (complex_norm_real hNX) k v Phi Psi Q T ->
  forall i j,q i j=weierstrass_ring_coefficient_step k phi psi i j q.
Proof.
move=>hPhi hPsi hQ hLow hLeading hDivision.
pose M: @holomorphic_germ_ring R X NX (complex_norm_real hNX) 0:=Phi*Q.
have [p hP]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX M v inclusion.
have [t hT]:=@complex_weierstrass_split_coefficients_exist R X K NX hNX T v inclusion.
have hHigh:=@complex_weierstrass_polynomial_high_coefficients R X K NX hNX k v inclusion T t
  (complex_weierstrass_division_polynomial_remainder hDivision) hT.
have hRemainder:T=Psi-M.
  rewrite /M (complex_weierstrass_division_identity hDivision) [Phi*Q]mulrC addrAC subrr add0r.
  reflexivity.
have hProduct:=@complex_weierstrass_split_coefficient_product R X K NX hNX Phi Q v inclusion phi q p hPhi hQ hP.
apply:(@weierstrass_ring_convolution_recursion (ComplexScalars.C R) K phi psi q k hLow hLeading)=>i j z.
have hLarge:(k<=i+k)%N by rewrite leq_addl.
have hDifference:@is_complex_weierstrass_split_coefficient R X K NX hNX
  (@HolomorphicGerms.add R X NX (complex_norm_real hNX) 0 Psi (@HolomorphicGerms.opp R X NX (complex_norm_real hNX) 0 M))
  v inclusion (i+k)%N j (t (i+k)%N j).
  change (is_complex_weierstrass_split_coefficient hNX (Psi-M) v inclusion (i+k)%N j (t (i+k)%N j)).
  rewrite -hRemainder;exact:hT (i+k)%N j.
have hValue:=@complex_weierstrass_split_coefficient_difference R X K NX hNX Psi M v inclusion
  (i+k)%N j (psi (i+k)%N j) (p (i+k)%N j) (t (i+k)%N j)
  (hPsi _ _) (hP _ _) hDifference z.
have hEqual:psi (i+k)%N j z=p (i+k)%N j z.
  apply/eqP;rewrite -subr_eq0;apply/eqP.
  by rewrite -hValue (hHigh _ hLarge j z).
rewrite hEqual hProduct.
apply:eq_bigr=>mu _;apply:eq_bigr=>nu _;exact:mulrC.
Qed.
