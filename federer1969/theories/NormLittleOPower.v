(** Federer (1969), 3.1.11, p. 221:
    a remainder is little-o of the kth
    scalar power along a line. The epsilon
    specification avoids dividing by a zero increment. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import RealNormUP NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_little_o_power]:
    the linewise remainder in the coefficient
    identification corollary of Federer 3.1.11,
    p. 221. For real nonzero t,
    this is equivalent to N(f(t))/|t|^k
    tending to zero. *)
Definition norm_little_o_power (R : realType) (Y : lmodType R)
    (N : Y->R) (f : R->Y) k :=
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall t, 0<`|t|<d -> N (f t)<=e*`|t|^+k.

(** Source for [norm_little_o_power_zero_limit]:
    a remainder of any nonnegative power
    tends to zero, supporting the coefficient
    identification in Federer 3.1.11, p. 221. *)
Lemma norm_little_o_power_zero_limit (R : realType) (Y : lmodType R)
    (N : Y->R) (f : R->Y) k :
  norm_little_o_power N f k -> punctured_norm_limit N f 0.
Proof.
move=>ho e he.
have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [r [hr hb]] := ho (e/2) he2.
exists (Num.min r 1); split; first by rewrite lt_min hr ltr01.
move=>t /andP [ht0 ht].
have hmr : Num.min r 1<=r by rewrite ge_min lexx.
have htr : `|t|<r := lt_le_trans ht hmr.
have ht1 : `|t|<=1.
  apply: le_trans (ltW ht) _; by rewrite ge_min lexx orbT.
have hp := exprn_ile1 k (ltW ht0) ht1.
have hh := le_trans (hb t (introT andP (conj ht0 htr))) (ler_wpM2l (ltW he2) hp).
rewrite subr0; apply: le_lt_trans hh _; rewrite mulr1; lra.
Qed.

(** Source for [norm_little_o_power_add]:
    finite addition of negligible remainders,
    supporting the Taylor coefficient comparison
    in Federer 3.1.11, p. 221. *)
Lemma norm_little_o_power_add (R : realType) (Y : lmodType R)
    (N : Y->R) (hN : is_real_norm N) (f g : R->Y) k :
  norm_little_o_power N f k -> norm_little_o_power N g k ->
  norm_little_o_power N (fun t=>f t+g t) k.
Proof.
move=>hf hg e he; have he2 : 0<e/2 by rewrite divr_gt0 // ltr0n.
have [r [hr hb]] := hf (e/2) he2.
have [s [hs hc]] := hg (e/2) he2.
exists (Num.min r s); split; first by rewrite lt_min hr hs.
move=>t /andP [ht0 ht].
have /andP [htr hts] : (`|t|<r)&&(`|t|<s) by rewrite -lt_min.
apply: le_trans (real_seminorm_triangle hN.1 _ _) _.
have hh := lerD (hb t (introT andP (conj ht0 htr))) (hc t (introT andP (conj ht0 hts))).
have hhalf : e/2+e/2=e by lra.
have heq : e/2*`|t|^+k+e/2*`|t|^+k=e*`|t|^+k by rewrite -mulrDl hhalf.
by rewrite heq in hh.
Qed.

(** Source for [norm_little_o_power_negate]:
    negating a negligible remainder preserves
    its order, supporting Federer 3.1.11, p. 221. *)
Lemma norm_little_o_power_negate (R : realType) (Y : lmodType R)
    (N : Y->R) (hN : is_real_norm N) (f : R->Y) k :
  norm_little_o_power N f k -> norm_little_o_power N (fun t=> -f t) k.
Proof.
move=>hf e he; have [d [hd hb]] := hf e he.
exists d; split=> // t ht; rewrite (real_seminorm_negate hN.1); exact: hb.
Qed.
