(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 332:
    the original monic equation and bounded
    numerators bound every transverse fibre
    coordinate. Reuse the scalar polynomial
    estimates and nonzero-denominator cancellation. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ComplexScalarSealed ComplexModulus ComplexModulusInverse MonicComplexPolynomialRootBound FiniteComplexPolynomialPowerBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [original_complex_polynomial_coordinate_bounds]:
    |omega_(m+1)|<=max(1,M), followed by
    the bounds for omega_j, j>m+1,
    3.4.12, p. 339, extending 3.4.8(10), p. 332. All original
    coordinates use the same M and
    denominator. No bounded-fibre conclusion is assumed. *)
Theorem original_complex_polynomial_coordinate_bounds (R:realType) k (index:finType) (first:index)
    (b0:'I_k->ComplexScalars.C R) (b:index->'I_k->ComplexScalars.C R)
    (delta:ComplexScalars.C R) (M:R) (y:index->ComplexScalars.C R):
  (0<k)%N ->0<M ->delta!=0 ->complex_modulus delta^-1<=M ->
  (\sum_(i<k) complex_modulus (b0 i))<=M ->(forall j,\sum_(i<k) complex_modulus (b j i)<=M) ->
  (y first)^+k+\sum_(i<k) b0 i*(y first)^+(i:nat) = 0 ->
  (forall j,j!=first ->delta*y j = \sum_(i<k) b j i*(y first)^+(i:nat)) ->
  complex_modulus (y first)<=Num.max 1 M /\
    forall j,j!=first ->complex_modulus (y j)<=M^+2*(Num.max 1 M)^+k.-1.
Proof.
move=>hK hM hDelta hInverse hB0 hB hRoot hRelations.
pose C:=Num.max 1 M.
have hC:1<=C by rewrite /C le_max lexx.
have hCNonnegative:0<=C:=le_trans ler01 hC.
have hFirst:complex_modulus (y first)<=C.
  apply:(le_trans (@monic_complex_polynomial_root_bound R k b0 (y first) hK hRoot)).
  rewrite /C ge_max;apply/andP;split;first by rewrite le_max lexx.
  apply:(le_trans hB0);by rewrite le_max lexx orbT.
split;first exact:hFirst.
move=>j hJ.
have hNumerator:=@finite_complex_polynomial_power_bound R k (b j) (y first) C hK hC hFirst.
have hPowerNonnegative:0<=C^+k.-1:=exprn_ge0 _ hCNonnegative.
have hNumeratorM:complex_modulus (\sum_(i<k) b j i*(y first)^+(i:nat))<=M*C^+k.-1.
  exact:(le_trans hNumerator (ler_wpM2r hPowerNonnegative (hB j))).
have hValue:y j=delta^-1*\sum_(i<k) b j i*(y first)^+(i:nat).
  by rewrite -(hRelations j hJ) mulrA mulVf // mul1r.
rewrite hValue complex_modulus_mul.
apply:(le_trans (ler_wpM2l (complex_modulus_ge0 (delta^-1)) hNumeratorM)).
have hBound:=ler_wpM2r (mulr_ge0 (ltW hM) hPowerNonnegative) hInverse.
rewrite expr2 -mulrA;exact:hBound.
Qed.
