(** Federer (1969), 2.4.14, p. 88: passage from equality of normalised
    absolute powers and a common product sign to dependence of signed
    powers. These are supporting real scalar identities. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower SignedRealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [equal_powers_nonnegative_product_signed]: the
    positive-product case of the final equality inference in Federer 2.4.14,
    p. 88 Zero scalar values are retained explicitly. *)
Lemma equal_powers_nonnegative_product_signed (R : realType) (p q x y : R) :
  0 < p -> 0 < q -> real_power `|x| p = real_power `|y| q -> 0 <= x*y ->
  signed_real_power p x = signed_real_power q y.
Proof.
move=> hp hq hpow hxy.
have [hx|hx] := eqVneq x 0.
- rewrite hx normr0 real_power_zero_base ?gt_eqF // in hpow.
  by rewrite hx signed_real_power_zero /signed_real_power -hpow mul0r.
have [hy|hy] := eqVneq y 0.
- rewrite hy normr0 real_power_zero_base ?gt_eqF // in hpow.
  by rewrite hy signed_real_power_zero /signed_real_power hpow mul0r.
have hxy0 : x*y != 0 by rewrite mulf_eq0 negb_or hx hy.
have hxypos : 0 < x*y by rewrite lt_neqAle eq_sym hxy0 hxy.
have he : Num.sg x * Num.sg y == 1 by rewrite -sgrM (gtr0_sg hxypos) eqxx.
move: he; rewrite mulr_sg_eq1=> /andP [_ /eqP hsign].
by rewrite /signed_real_power hpow hsign.
Qed.

(** Source for [equal_powers_nonpositive_product_signed]: the
    negative-product case of the final equality inference in Federer 2.4.14,
    p. 88 Negating one factor reduces it to the preceding positive-product
    argument. *)
Lemma equal_powers_nonpositive_product_signed (R : realType) (p q x y : R) :
  0 < p -> 0 < q -> real_power `|x| p = real_power `|y| q -> x*y <= 0 ->
  signed_real_power p x = -signed_real_power q y.
Proof.
move=> hp hq hpow hxy.
have hpow' : real_power `|x| p = real_power `|-y| q by rewrite normrN.
have hxy' : 0 <= x*(-y) by rewrite mulrN oppr_ge0.
have h := @equal_powers_nonnegative_product_signed R p q x (-y) hp hq hpow' hxy'.
by rewrite signed_real_power_negate in h.
Qed.
