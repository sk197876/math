(** Federer 2.10.2, p. 171: small positive enlargements preserve a
    strict upper bound on the real-degree gauge. Supporting scalar step
    for the open-cover and positive-radius ball comparisons. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealPower RealPowerContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_power_gauge_small_enlargement]: Federer 2.10.2,
    p. 171, supporting continuity argument for all nonnegative real
    degrees. Zero starting diameter and exponent zero are included. *)
Lemma real_power_gauge_small_enlargement (R:realType) (c p d t b:R):
  0<c -> 0<=p -> 0<=d -> d<t -> c*real_power d p<b ->
  exists r:R, 0<r /\ d+r+r<t /\ c*real_power (d+r+r) p<b.
Proof.
move=> hc hp hd hdt hb.
have h4 : (0<4:>R) by rewrite ltr0n.
case: (eqVneq p 0)=>[hp0|hpne].
- subst p.
  exists ((t-d)/4); split.
  + rewrite divr_gt0 // subr_gt0; exact:hdt.
  + split.
    * have hh : (t-d)/4*4=t-d by rewrite divfK ?pnatr_eq0.
      lra.
    * by rewrite ?real_power_zero_exponent in hb *.
have hpp:0<p by rewrite lt_neqAle eq_sym hpne hp.
pose e:=(b-c*real_power d p)/c.
have he:0<e by rewrite /e divr_gt0 // subr_gt0.
have [delta hdelta hBound] := real_power_local_bound hd hpp he.
pose r:=Order.min (delta/4) ((t-d)/4).
have hr:0<r by rewrite /r lt_min !divr_gt0 // subr_gt0.
have hrD:r<=delta/4 by rewrite /r ge_min lexx.
have hrT:r<=(t-d)/4 by rewrite /r ge_min lexx orbT.
have hD:delta/4*4=delta by rewrite divfK ?pnatr_eq0.
have hT:(t-d)/4*4=t-d by rewrite divfK ?pnatr_eq0.
have hy:0<=d+r+r by lra.
have hDist:`|d-(d+r+r)|<delta.
  have heq:d-(d+r+r)= -(r+r) by lra.
  rewrite heq normrN ger0_norm; lra.
have hPow:=hBound (d+r+r) hy hDist.
have hErr:=ler_norm (real_power (d+r+r) p-real_power d p).
rewrite distrC in hErr.
have hMul : c*(real_power (d+r+r) p-real_power d p)<c*e.
  rewrite (ltr_pM2l hc); exact:le_lt_trans hErr hPow.
have heq:e*c=b-c*real_power d p by rewrite /e divfK ?gt_eqF.
exists r; split=>//; split; nra.
Qed.
