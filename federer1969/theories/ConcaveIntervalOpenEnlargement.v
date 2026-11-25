(** Federer (1969), 2.10.28(3), p. 192. This file proves the single
    generator step. Use the existing family of bounded nonempty open
    intervals from 2.10.7; its carrier does not depend on a Stieltjes
    integrator. No witness operator is selected globally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge ConcaveIntervalGaugeUP StieltjesCaratheodoryUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [concave_interval_open_enlargement_exists]: supporting open
    interval enlargement in the compact-cover lower mass argument of
    2.10.28(3), p. 192 The original compact interval may be a singleton,
    while the containing open interval is always nonempty and bounded. *)
Lemma concave_interval_open_enlargement_exists (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (S : compact_real_intervals R) (e : R) :
  0<e -> exists U : stieltjes_open_intervals R,
    val S `<=` stieltjes_interval_set U /\
    h ((val U).2-(val U).1)<concave_interval_cost h (val S)+e.
Proof.
move=> he; have [a [b [hab hS]]] := set_valP S.
pose d := b-a.
have hd : 0<=d by rewrite /d subr_ge0.
have [r [hr hcontrol]] := @interval_gauge_continuity R h hg d e hd he.
pose t := r/4.
have ht : 0<t by rewrite /t divr_gt0 // ltr0n.
have horder : a-t<b+t by lra.
pose U : stieltjes_open_intervals R := Sub (a-t,b+t) (mem_set horder).
have hlen : (b+t)-(a-t)=d+2*t by rewrite /d; lra.
have hnew0 : 0<=(b+t)-(a-t) by rewrite subr_ge0; exact: ltW horder.
have herrorid : ((b+t)-(a-t))-d = 2*t by rewrite hlen; lra.
have herr : `|((b+t)-(a-t))-d|<r.
  rewrite herrorid ger0_norm; last by lra.
  by rewrite /t; lra.
have hcostcontrol := hcontrol ((b+t)-(a-t)) hnew0 herr.
have hdiff := le_lt_trans (ler_norm (h ((b+t)-(a-t))-h d)) hcostcontrol.
exists U; split.
- rewrite hS; move=> x hx.
  have /andP[hax hxb] : a<=x<=b by move: hx; rewrite /= in_itv.
  change (`]a-t,b+t[ x); rewrite /= in_itv /=; apply/andP; split; lra.
- change (h ((b+t)-(a-t))<concave_interval_cost h (val S)+e).
  rewrite hS concave_interval_cost_segment //; change (h ((b+t)-(a-t))<h d+e); lra.
Qed.
