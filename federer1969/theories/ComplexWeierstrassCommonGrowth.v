(** Federer (1969), 3.4.12, p. 339: both original
    complex input families admit common geometric constants.
    Apply the existing real numerical theorem to their actual
    nonnegative modulus functions; do not repeat its inequalities. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ComplexScalarSealed ComplexModulus WeierstrassCommonGrowth.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [complex_weierstrass_common_coefficient_growth]: the
    common original coefficient bounds needed for complex division,
    extending 3.4.6, p. 324, under 3.4.12, p. 339. *)
Lemma complex_weierstrass_common_coefficient_growth (R:realType) (K:Type) (P:K->Prop)
    (phi psi:nat->nat->K->ComplexScalars.C R) (b1 c1 b2 c2:R):
  0<b1 ->0<c1 ->0<b2 ->0<c2 ->
  (forall i j z,P z ->complex_modulus (phi i j z)<=b1*c1^+(i+j)) ->
  (forall i j z,P z ->complex_modulus (psi i j z)<=b2*c2^+(i+j)) ->
  exists b c:R,0<b /\0<c /\
    (forall i j z,P z ->complex_modulus (phi i j z)<=b*c^+(i+j)) /\
    (forall i j z,P z ->complex_modulus (psi i j z)<=b*c^+(i+j)).
Proof.
move=>hb1 hc1 hb2 hc2 hPhi hPsi.
have hFirst i j z:P z ->`|complex_modulus (phi i j z)|<=b1*c1^+(i+j).
  by move=>hz;rewrite ger0_norm ?complex_modulus_ge0 //;exact:hPhi i j z hz.
have hSecond i j z:P z ->`|complex_modulus (psi i j z)|<=b2*c2^+(i+j).
  by move=>hz;rewrite ger0_norm ?complex_modulus_ge0 //;exact:hPsi i j z hz.
have [b [c [hb [hc [hP hQ]]]]]:=@weierstrass_common_coefficient_growth R K P
  (fun i j z=>complex_modulus (phi i j z)) (fun i j z=>complex_modulus (psi i j z))
  b1 c1 b2 c2 hb1 hc1 hb2 hc2 hFirst hSecond.
exists b,c;split;first exact:hb.
split;first exact:hc.
split=>i j z hz.
- have h:=hP i j z hz;by rewrite ger0_norm ?complex_modulus_ge0 in h.
- have h:=hQ i j z hz;by rewrite ger0_norm ?complex_modulus_ge0 in h.
Qed.
