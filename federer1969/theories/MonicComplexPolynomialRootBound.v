(** Federer (1969), 3.4.12, p. 339, extending the root bound
    in 3.4.8(10), p. 332: a complex root is bounded by
    one or the sum of the original lower coefficient moduli.
    MonicRealPolynomialRootBound applies only to real roots. Use its
    ordered-power argument with the existing complex norm laws; the
    original complex polynomial and every positive degree remain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Roots.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation N:=(@complex_modulus R).
Local Notation hN:=(@complex_modulus_real_norm R).
(** Source for [complex_modulus_power]: multiplicativity gives the
    modulus of every original scalar power, supporting the root
    bound in 3.4.12, p. 339. *)
Lemma complex_modulus_power (z:C) k:N (z^+k)=(N z)^+k.
Proof.
elim:k=>[|k IH];first by rewrite !expr0 -(rmorph1 (ComplexScalars.embed R)) complex_modulus_real normr1.
by rewrite !exprS complex_modulus_mul IH.
Qed.
(** Source for [monic_complex_polynomial_root_bound]: the original
    first complex coordinate has the required finite bound for
    compact polynomial fibres, 3.4.12, p. 339. *)
Theorem monic_complex_polynomial_root_bound k (b:'I_k->C) (z:C):
  (0<k)%N ->z^+k+\sum_(i<k) b i*z^+(i:nat)=0 ->
  N z<=Num.max 1 (\sum_(i<k) N (b i)).
Proof.
move=>hK hEquation.
pose M:=\sum_(i<k) N (b i).
case:(leP (N z) 1)=>hSmall.
- apply:(le_trans hSmall);by rewrite le_max lexx.
have hNormPositive:0<N z:=lt_trans ltr01 hSmall.
have hAtLeastOne:1<=N z:=ltW hSmall.
have hEquality:z^+k = -\sum_(i<k) b i*z^+(i:nat).
  have h:=congr1 (fun x:C=>x-\sum_(i<k) b i*z^+(i:nat)) hEquation.
  by rewrite addrK sub0r in h.
have hNorm:(N z)^+k=N (\sum_(i<k) b i*z^+(i:nat)).
  rewrite -complex_modulus_power hEquality.
  exact:(@real_seminorm_negate R CR N hN.1 _).
have hSum:N (\sum_(i<k) b i*z^+(i:nat))<=M*(N z)^+k.-1.
  apply:(le_trans (@real_seminorm_sum R CR N hN.1 [the finType of 'I_k]
    (fun i=>b i*z^+(i:nat)))).
  rewrite /M mulr_suml;apply:ler_sum=>i _.
  rewrite complex_modulus_mul complex_modulus_power.
  apply:ler_wpM2l;first exact:complex_modulus_ge0.
  apply:(ler_weXn2l hAtLeastOne).
  have hBoundNat:forall j:nat,(j<k)%N ->(j<=k.-1)%N.
    move=>j;by rewrite -(prednK hK) ltnS.
  exact:hBoundNat (i:nat) (ltn_ord i).
have hPowerPositive:0<(N z)^+k.-1:=exprn_gt0 _ hNormPositive.
have hCancel:N z<=M.
  rewrite -(ler_pM2r hPowerPositive) -exprS (prednK hK) hNorm.
  exact:hSum.
apply:(le_trans hCancel);by rewrite le_max lexx orbT.
Qed.
End Roots.
