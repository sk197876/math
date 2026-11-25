(** Federer (1969), 4.1.1, pp. 344–345: a continuous linear
    functional is bounded by a finite multiple of one defining
    seminorm. This supporting scaling argument also applies to
    seminorms and includes a zero seminorm. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [seminorm_unit_ball_domination]: supporting homogeneity
    argument behind the finite seminorm bounds in Federer 4.1.1,
    pp. 344–345. A bound on one positive-radius ball gives a global
    multiple without assuming positive definiteness. *)
Theorem seminorm_unit_ball_domination (R:realType) (E:lmodType R)
    (p q:E->R) (hp:is_real_seminorm p) (hq:is_real_seminorm q) (d:R) :
  0<d -> (forall x,p x<d -> q x<1) ->
  forall x, q x <= (2/d) * p x.
Proof.
move=>hd hb x.
have hp0:=real_seminorm_nonnegative hp x.
have hq0:=real_seminorm_nonnegative hq x.
have hC:0<2/d by rewrite divr_gt0 // ltr0n.
case:(eqVneq (p x) 0)=>[hpx|hpx].
- rewrite hpx mulr0.
  have [hqx|hqx]:=eqVneq (q x) 0; first by rewrite hqx.
  have hqpos:0<q x by rewrite lt_def hqx hq0.
  pose t:=2/q x.
  have ht:0<t by rewrite /t divr_gt0 // ltr0n.
  have hsmall:p (t*:x)<d.
    by rewrite (real_seminorm_scale hp) hpx mulr0.
  have h:=hb _ hsmall.
  rewrite (real_seminorm_scale hq) (ger0_norm (ltW ht)) /t
    divfK ?gt_eqF // in h.
  by nra.
- have hppos:0<p x by rewrite lt_def hpx hp0.
  pose t:=d/(2* p x).
  have ht:0<t by rewrite /t divr_gt0 // mulr_gt0 // ltr0n.
  have hpxscaled:p (t*:x)=d/2.
    rewrite (real_seminorm_scale hp) (ger0_norm (ltW ht)) /t invfM mulrA.
    by rewrite divfK // gt_eqF.
  have hsmall:p (t*:x)<d by rewrite hpxscaled; lra.
  have h:=hb _ hsmall.
  rewrite (real_seminorm_scale hq) (ger0_norm (ltW ht)) in h.
  have hbound:q x<t^-1 by rewrite -div1r ltr_pdivlMr // mulrC.
  apply:ltW; apply:lt_le_trans hbound _.
  by rewrite /t invf_div mulrAC.
Qed.
