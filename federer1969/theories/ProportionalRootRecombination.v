(** Federer (1969), 3.2.41, printed p. 277, last displayed
    finite-family induction step: equal relative masses on the
    two sides make their powered lower bounds sum to the original
    powered bound. This supporting scalar lemma proves that step. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealPower RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [proportional_two_piece_root_recombination]: supporting
    recombination in Federer 3.2.41, p. 277. All masses and both
    fractions may be zero. The positive real exponent p generalizes
    the printed positive integer n; the application uses p=n.
    No powered comparison is assumed in place of a root comparison. *)
Lemma proportional_two_piece_root_recombination (R:realType)
    (p a b c c1 c2 t:R):
  0<p ->0<=a ->0<=b ->0<=c1 ->0<=c2 ->0<=t ->t<=1 ->
  c1+c2<=c ->
  real_power (t*a) p^-1+real_power (t*b) p^-1<=real_power c1 p^-1 ->
  real_power ((1-t)*a) p^-1+real_power ((1-t)*b) p^-1<=real_power c2 p^-1 ->
  real_power a p^-1+real_power b p^-1<=real_power c p^-1.
Proof.
move=> hp ha hb hc1 hc2 ht ht1 hSum hOne hTwo.
pose q:=real_power a p^-1+real_power b p^-1.
have hq:0<=q by rewrite /q; apply:addr_ge0; exact:real_power_nonnegative.
have htc:0<=1-t by rewrite subr_ge0.
have hScaled u:0<=u ->
    real_power (u*a) p^-1+real_power (u*b) p^-1=real_power u p^-1*q.
  move=> hu; rewrite !real_power_product // /q; ring.
rewrite (hScaled t ht) in hOne.
rewrite (hScaled (1-t) htc) in hTwo.
have hFirst:=@real_power_monotone R (real_power t p^-1*q) (real_power c1 p^-1) p
  (mulr_ge0 (real_power_nonnegative t p^-1) hq) hOne hp.
have hSecond:=@real_power_monotone R (real_power (1-t) p^-1*q) (real_power c2 p^-1) p
  (mulr_ge0 (real_power_nonnegative (1-t) p^-1) hq) hTwo hp.
rewrite real_power_product ?real_power_nonnegative //
  (real_power_inverse_power ht hp) (real_power_inverse_power hc1 hp) in hFirst.
rewrite real_power_product ?real_power_nonnegative //
  (real_power_inverse_power htc hp) (real_power_inverse_power hc2 hp) in hSecond.
have hCombine:=le_trans (lerD hFirst hSecond) hSum.
have he:t*real_power q p+(1-t)*real_power q p=real_power q p by ring.
rewrite he in hCombine.
have hFinal:=@real_power_monotone R (real_power q p) c p^-1
  (real_power_nonnegative q p) hCombine (ltac:(by rewrite invr_gt0)).
by rewrite (real_power_root_cancel hq hp) in hFinal.
Qed.
