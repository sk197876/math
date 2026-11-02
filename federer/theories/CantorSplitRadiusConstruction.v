(** Federer (1969), 2.10.28(4), pp. 192–193: existence of the abstract
    equal-cost child length. Apply the intermediate value theorem on [0,d]
    to h(d)/n, then use strict concavity to obtain s<d/n. The intermediate
    value theorem is general topology of the real line. No external Cantor
    construction is imported. This witness will be hidden behind opaque
    module ascription. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws CantorSplitRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_gauge_segment_continuous]: supporting
    relative continuity for the intermediate value
    step in 2.10.28(4), p. 192,
    from the specified epsilon-delta law. Continuity
    outside the nonnegative real axis is not assumed. *)
Lemma interval_gauge_segment_continuous (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (a b : R) : 0<=a ->
  {within (`[a,b] : set (real_line_metric R)),
    continuous (h : real_line_metric R -> real_line_metric R)}.
Proof.
move=> ha; apply/subspace_continuousP=> x hx; apply/cvg_ballP=> e he.
have /andP[hax hxb] : a<=x<=b by move: hx; rewrite /= in_itv.
have hx0 : 0<=x := le_trans ha hax.
have [d [hd hcontrol]] := @interval_gauge_continuity R h hg x e hx0 he.
change (nbhs (x : real_line_metric R)
  [set y | `[a,b] y -> ball (h x : real_line_metric R) e (h y)]).
apply: (filterS _ (nbhsx_ballx (x : real_line_metric R) d hd))=> y hy hyA.
have /andP[hay hyb] : a<=y<=b by move: hyA; rewrite /= in_itv.
have hy0 : 0<=y := le_trans ha hay.
have hyx : `|y-x|<d by move: hy; rewrite /ball /= distrC.
change (`|h x-h y|<e); rewrite distrC; exact: hcontrol y hy0 hyx.
Qed.

(** Source for [cantor_split_radius_exists]: supporting existence of s in
    2.10.28(4), p. 192, under the nondegenerate parent hypothesis explicit.
    Strict dilation gives the strict diameter bound. *)
Theorem cantor_split_radius_exists (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (d : R) n :
  0<d -> (2<=n)%N -> exists s, is_cantor_split_radius h d n s.
Proof.
move=> hd hn.
pose N := (n%:R : R).
have hN1 : 1<N by rewrite /N ltr1n.
have hN : 0<N := lt_trans ltr01 hN1.
have hN0 : N!=0 by rewrite gt_eqF.
have hpos := @concave_interval_gauge_strictly_increasing R h hg 0 d (lexx 0) hd.
rewrite (interval_gauge_zero hg) in hpos.
pose v := h d/N.
have hv0 : 0<v by rewrite /v divr_gt0.
have hNi1 : N^-1<1 by rewrite invf_lt1.
have hvhi : v<h d.
  change (h d*N^-1<h d); rewrite -[X in _<X]mulr1 (ltr_pM2l hpos); exact hNi1.
have hc := @interval_gauge_segment_continuous R h hg 0 d (lexx 0).
have hbounds : Order.min (h 0) (h d)<=v<=Order.max (h 0) (h d).
  by rewrite (interval_gauge_zero hg) min_l ?max_r ?(ltW hpos) // (ltW hv0) (ltW hvhi).
have [s hs hsvalue] := @IVT R h 0 d v (ltW hd) hc hbounds.
have /andP[hs0 hsd] : 0<=s<=d by move: hs; rewrite in_itv.
have hspos : 0<s.
  rewrite lt_neqAle eq_sym hs0 andbT; apply/eqP=> hz.
  rewrite hz (interval_gauge_zero hg) in hsvalue.
  by rewrite -hsvalue ltxx in hv0.
have hstrict := @concave_interval_gauge_strict_dilation R h hg s N hspos hN1.
have hcancel : N*h s=h d by rewrite hsvalue /v mulrC divfK.
rewrite hcancel in hstrict.
have hlength : N*s<d.
  rewrite ltNge; apply/negP=> hle.
  have hh := @interval_gauge_increasing R h hg d (N*s) (ltW hd) hle.
  by have hf := lt_le_trans hstrict hh; rewrite ltxx in hf.
exists s; constructor; last exact hsvalue.
split=> //; change (s<d/N); by rewrite ltr_pdivlMr // mulrC.
Qed.
