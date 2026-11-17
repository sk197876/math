(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), p. 332:
    bound each bounded-degree numerator on the
    original finite root interval. Apply the
    scalar norm-sum and monotone-power laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm ComplexModulusFiniteSum ComplexModulusPowers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_complex_polynomial_power_bound]:
    the bound M sup(1,M^(k-1))
    for the original numerator polynomials,
    3.4.12, p. 339, extending 3.4.8(10), p. 332. Every positive
    degree and arbitrary complex coefficients remain. *)
Theorem finite_complex_polynomial_power_bound (R:realType) k (b:'I_k->ComplexScalars.C R) (t:ComplexScalars.C R) (C:R):
  (0<k)%N ->1<=C ->complex_modulus t<=C ->
  complex_modulus (\sum_(i<k) b i*t^+(i:nat))<=(\sum_(i<k) complex_modulus (b i))*C^+k.-1.
Proof.
move=>hK hC hT.
have hCNonnegative:0<=C:=le_trans ler01 hC.
apply:(le_trans (@complex_modulus_finite_sum R [the finType of 'I_k] (fun i=>b i*t^+(i:nat)))).
rewrite mulr_suml;apply:ler_sum=>i _.
rewrite complex_modulus_mul complex_modulus_power;apply:ler_wpM2l;first exact:complex_modulus_ge0.
apply:(le_trans (lerXn2r (i:nat) (complex_modulus_ge0 t) hCNonnegative hT)).
apply:(ler_weXn2l hC).
have hBoundNat:forall j:nat,(j<k)%N ->(j<=k.-1)%N.
  move=>j;by rewrite -(prednK hK) ltnS.
exact:hBoundNat (i:nat) (ltn_ord i).
Qed.
