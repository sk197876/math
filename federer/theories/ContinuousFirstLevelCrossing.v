(** Federer (1969), 3.2.46, printed p. 281: supporting first-exit
    times for the local comparison of lengths. Prove an actual level
    hit with a whole controlled prefix. Continuity is only relative
    to the original compact interval; no global extension is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra
  classical_sets topology.
From Federer Require Import RealMetricBackground CurveFirstLevelCrossing
  SegmentContinuityControl.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_first_level_crossing]: supporting the
    first controlled collar of an escaping curve in Federer 3.2.46,
    p. 281. The first hit is strictly between the endpoints, its
    value is exactly the required level, and the entire preceding
    closed interval stays at or below that level. *)
Theorem continuous_first_level_crossing (R : realType) (f : R -> R)
    (a b q : R) :
  a <= b ->
  {within (`[a,b] : set (real_line_metric R)),
    continuous (f : real_line_metric R -> real_line_metric R)} ->
  f a < q -> q < f b -> exists u : R,
    a < u < b /\ f u = q /\ forall t, a <= t <= u -> f t <= q.
Proof.
move=> hab hc hfa hfb.
have [u [/andP[hau hub] [hBefore hAfter]]] :=
  (@first_curve_level_crossing_exists R f a b q hab hfb).
have hLow : q <= f u.
  rewrite leNgt; apply/negP=> hfu.
  pose e := (q-f u)/2.
  have he : 0 < e by rewrite /e divr_gt0 ?subr_gt0 // ltr0n.
  have [d [hd hControl]] := (@segment_continuity_epsilon_control R f a b u e hc hau hub he).
  have [t [/andP[hut htb] [htd hqt]]] := hAfter d hd.
  have hta : a <= t := le_trans hau hut.
  have hClose : `|t-u| < d by rewrite ger0_norm ?subr_ge0 //; lra.
  have hVal := hControl t hta htb hClose.
  have hLe := ler_norm (f t-f u).
  have hDiff : f t-f u < e := le_lt_trans hLe hVal.
  rewrite /e in hDiff; lra.
have hauStrict : a < u.
  rewrite lt_neqAle hau andbT; apply/negP=> /eqP hauEq.
  have hBad := lt_le_trans hfa hLow.
  by rewrite hauEq ltxx in hBad.
have hHigh : f u <= q.
  rewrite leNgt; apply/negP=> hfu.
  pose e := (f u-q)/2.
  have he : 0 < e by rewrite /e divr_gt0 ?subr_gt0 // ltr0n.
  have [d [hd hControl]] := (@segment_continuity_epsilon_control R f a b u e hc hau hub he).
  pose r := Order.min (d/2) ((u-a)/2).
  have hr : 0 < r by rewrite /r lt_min !divr_gt0 ?subr_gt0 // ltr0n.
  have hrd : r <= d/2 by rewrite /r ge_min lexx.
  have hra : r <= (u-a)/2 by rewrite /r ge_min lexx orbT.
  pose t := u-r.
  have hta : a <= t by rewrite /t; lra.
  have htu : t < u by rewrite /t ltrBlDr ltrDl.
  have htb : t <= b := le_trans (ltW htu) hub.
  have hClose : `|t-u| < d.
    have hEq : t-u = -r by rewrite /t; lra.
    rewrite hEq normrN ger0_norm; lra.
  have hVal := hControl t hta htb hClose.
  have hPre : f t <= q := hBefore t hta htu.
  have hLe : f u-f t <= `|f t-f u|.
    rewrite distrC; exact: ler_norm.
  have hDiff : f u-f t < e := le_lt_trans hLe hVal.
  rewrite /e in hDiff; lra.
have hValue : f u = q by apply/eqP; rewrite eq_le hHigh hLow.
have hubStrict : u < b.
  rewrite lt_neqAle hub andbT; apply/negP=> /eqP hubEq.
  have hBad := hfb; by rewrite -hubEq hValue ltxx in hBad.
exists u; split; first by apply/andP.
split=> // t /andP[hat htu].
case: (ltP t u)=> hStrict; first exact: hBefore t hat hStrict.
have htEq : t = u by apply/eqP; rewrite eq_le htu hStrict.
by rewrite htEq hValue.
Qed.
