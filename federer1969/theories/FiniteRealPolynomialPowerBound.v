(** Federer (1969), 3.4.8(10), p. 332:
    bound each bounded-degree numerator on the
    original finite root interval. Apply the
    scalar norm-sum and monotone-power laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_real_polynomial_power_bound]:
    the bound M sup(1,M^(k-1))
    for the original numerator polynomials,
    3.4.8(10), p. 332. Every positive
    degree and arbitrary real coefficients remain. *)
Theorem finite_real_polynomial_power_bound (R:realType) k (b:'I_k->R) (t C:R):
  (0<k)%N ->1<=C ->`|t|<=C ->
  `|\sum_(i<k) b i*t^+(i:nat)|<=(\sum_(i<k) `|b i|)*C^+k.-1.
Proof.
move=>hK hC hT.
have hCNonnegative:0<=C:=le_trans ler01 hC.
apply:(le_trans (ler_norm_sum _ _ _)).
rewrite mulr_suml;apply:ler_sum=>i _.
rewrite normrM normrX;apply:ler_wpM2l;first exact:normr_ge0.
apply:(le_trans (lerXn2r (i:nat) (normr_ge0 t) hCNonnegative hT)).
apply:(ler_weXn2l hC).
have hBoundNat:forall j:nat,(j<k)%N ->(j<=k.-1)%N.
  move=>j;by rewrite -(prednK hK) ltnS.
exact:hBoundNat (i:nat) (ltn_ord i).
Qed.
