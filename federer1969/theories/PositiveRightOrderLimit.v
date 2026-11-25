(** Federer (1969), 2.5.3, p. 94, first display: a limit as the positive
    real width h tends to zero. This supporting order-topological
    specification and its cofinality lemma make the arbitrary-width limit
    explicit; they are infrastructure, not separate claims attributed to
    Federer. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit ExtendedRealReciprocalBounds
  RealLatticeTruncationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [positive_right_extended_order_limit]: supporting precise
    right-hand limit in Federer 2.5.3, p. 94 The value is extended real,
    with one-sided order neighbourhoods at either infinity. *)
Definition positive_right_extended_order_limit (R : realType) (u : R -> \bar R) l :=
  (forall a, a < l -> exists d : R, (0 < d)%R /\
    forall h, (0 < h)%R -> (h < d)%R -> a < u h) /\
  (forall b, l < b -> exists d : R, (0 < d)%R /\
    forall h, (0 < h)%R -> (h < d)%R -> u h < b).

(** Source for [positive_right_extended_order_limit_congr]: supporting
    replacement by equal positive-width expressions in Federer 2.5.3, p. 94
    Values at zero or at negative widths do not affect the limit. *)
Lemma positive_right_extended_order_limit_congr (R : realType)
    (u v : R -> \bar R) l :
  (forall h, (0 < h)%R -> u h=v h) ->
  positive_right_extended_order_limit u l -> positive_right_extended_order_limit v l.
Proof.
move=> he [hlo hup]; split.
- move=> a ha; have [d [hd hD]] := hlo a ha; exists d; split=> // h hh hhd.
  rewrite -(he h hh); exact: hD h hh hhd.
- move=> b hb; have [d [hd hD]] := hup b hb; exists d; split=> // h hh hhd.
  rewrite -(he h hh); exact: hD h hh hhd.
Qed.

(** Source for [antitone_reciprocal_positive_right_limit]: cofinal
    reciprocal widths for the monotone cutoff limit in Federer 2.5.3, p. 94
    Monotonicity transfers the sequence limit to every positive width
    tending to zero, including infinite limits. *)
Lemma antitone_reciprocal_positive_right_limit (R : realType)
    (u : R -> \bar R) l :
  (forall h k, (0 < h)%R -> (0 < k)%R -> (h <= k)%R -> u k <= u h) ->
  extended_order_limit (fun n => u (((n.+1)%:R)^-1)%R) l ->
  positive_right_extended_order_limit u l.
Proof.
move=> hmono [hlo hup].
have hp n : (0 < ((n.+1)%:R : R)^-1)%R by rewrite invr_gt0 ltr0n.
split.
- move=> a ha; have [N hN] := hlo a ha.
  exists (((N.+1)%:R)^-1)%R; split; first exact: hp.
  move=> h hh hhd; apply: lt_le_trans (hN N (leqnn N)) _.
  exact: (hmono h (((N.+1)%:R)^-1)%R hh (hp N) (ltW hhd)).
- move=> b hb; have [M hM] := hup b hb.
  exists 1%R; split; first exact: ltr01.
  move=> h hh hsmall; have [N hN] := positive_reciprocal_nat_small hh.
  have hwidth : (((((maxn N M).+1)%:R : R)^-1) <= h)%R.
    apply: le_trans (@positive_reciprocal_nat_antitone R N (maxn N M) (leq_maxl N M)) _.
    exact: ltW hN.
  apply: le_lt_trans (hmono _ h (hp (maxn N M)) hh hwidth) _.
  exact: hM (maxn N M) (leq_maxr N M).
Qed.
