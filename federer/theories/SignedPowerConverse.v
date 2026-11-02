(** Federer (1969), 2.4.14, p. 88: recovering equality of absolute powers
    and a product sign from signed power equality. Supporting scalar
    converse identities include zero values. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower SignedRealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [signed_real_power_sign]: preservation of sign
    by positive signed powers, supporting Federer 2.4.14,
    p. 88, and its almost-dependence criterion. *)
Lemma signed_real_power_sign (R : realType) (p x : R) :
  0 < p -> Num.sg (signed_real_power p x) = Num.sg x.
Proof.
move=> hp; have [->|hx] := eqVneq x 0.
- by rewrite signed_real_power_zero.
have hxpos : 0 < `|x| by rewrite normr_gt0.
have hpow := @real_power_strictly_positive R `|x| p hxpos.
by rewrite /signed_real_power sgrM (gtr0_sg hpow) mul1r sgr_id.
Qed.

(** Source for [signed_power_equality_absolute_and_sign]: the scalar
    converse behind the positive coefficient equality case in Federer
    2.4.14, p. 88 *)
Lemma signed_power_equality_absolute_and_sign (R : realType) (p q x y : R) :
  0 < p -> 0 < q -> signed_real_power p x = signed_real_power q y ->
  real_power `|x| p = real_power `|y| q /\ 0 <= x*y.
Proof.
move=> hp hq he; split.
- have hn := congr1 (fun z : R => `|z|) he.
  by rewrite !signed_real_power_absolute // in hn.
- have hs := congr1 (fun z : R => Num.sg z) he.
  rewrite !signed_real_power_sign // in hs.
  rewrite -sgr_ge0 sgrM hs -expr2; exact: sqr_ge0.
Qed.

(** Source for [signed_power_opposite_absolute_and_sign]: the scalar
    converse for the negative coefficient case in Federer 2.4.14, p. 88 *)
Lemma signed_power_opposite_absolute_and_sign (R : realType) (p q x y : R) :
  0 < p -> 0 < q -> signed_real_power p x = -signed_real_power q y ->
  real_power `|x| p = real_power `|y| q /\ x*y <= 0.
Proof.
move=> hp hq he.
have he' : signed_real_power p x = signed_real_power q (-y) by rewrite signed_real_power_negate.
have [hpow hxy] := @signed_power_equality_absolute_and_sign R p q x (-y) hp hq he'.
rewrite normrN in hpow; split=> //; by move: hxy; rewrite mulrN oppr_ge0.
Qed.
