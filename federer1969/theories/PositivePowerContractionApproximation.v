(** Federer (1969), 3.2.43, printed p. 278:
    strict inner-volume thresholds approximate the printed
    fractional power of the positive original volume. The
    zero exponent in dimension one is retained explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonnegative_exponent_power_monotone]: supporting
    inner-core volume comparison in Federer 3.2.43, p. 278.
    The exponent may vanish; the positive-exponent result
    is already proved for 2.4.12, pp. 86--87. *)
Lemma nonnegative_exponent_power_monotone (R:realType) (a b p:R):
  0<=a ->a<=b ->0<=p ->real_power a p<=real_power b p.
Proof.
move=>ha hab hp.
have [hp0|hp0]:=eqVneq p 0.
- by rewrite hp0 !real_power_zero_exponent.
- have hPos:0<p by rewrite lt_neqAle eq_sym hp0 hp.
  exact:real_power_monotone ha hab hPos.
Qed.

(** Source for [positive_power_contraction_threshold_exists]:
    supporting approximation of the positive closure-volume
    power in Federer 3.2.43, p. 278. For every contraction
    0<t<1 a genuinely smaller positive mass q<a has power
    at least t*a^p. For p=0 choose a/2; otherwise take
    the local witness a*t^(1/p). No global threshold is selected. *)
Lemma positive_power_contraction_threshold_exists (R:realType) (a p t:R):
  0<a ->0<=p ->0<t<1 ->
  exists q:R,0<q /\q<a /\t*real_power a p<=real_power q p.
Proof.
move=>ha hp /andP[ht0 ht1].
have [hp0|hp0]:=eqVneq p 0.
- exists (a/2); split.
  + by rewrite divr_gt0.
  + split.
    * by rewrite ltr_pdivrMr // ltr_pMr // ltr1n.
    * by rewrite hp0 !real_power_zero_exponent mulr1; exact:ltW ht1.
- have hPos:0<p by rewrite lt_neqAle eq_sym hp0 hp.
  pose u:=real_power t p^-1.
  have hu:0<u:=real_power_strictly_positive _ ht0.
  have hu1:u<1.
    have hi:0<p^-1 by rewrite invr_gt0.
    have h:=@real_power_strict_monotone R t 1 p^-1 (ltW ht0) ht1 hi.
    by rewrite real_power_one_base in h.
  exists (a*u); split; first exact:mulr_gt0 ha hu.
  split.
  + by rewrite -[X in _<X]mulr1 ltr_pM2l.
  + rewrite (@real_power_product R a u p (ltW ha) (ltW hu)) /u
      (real_power_inverse_power (ltW ht0) hPos).
    by rewrite mulrC.
Qed.
