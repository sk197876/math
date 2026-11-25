(** Supporting reciprocal primitive for the elementary calculations in
    Federer (1969), 2.6.3(2), pp. 117–118 The proof uses the exact
    reciprocal-increment identity and uniform continuity on a compact
    segment, not an imported differentiation rule. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology normedtype ring lra.
From Federer Require Import UniformPrimitiveUP SegmentUniformContinuity ContinuousSegmentBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [affine_reciprocal_uniform_primitive]: supporting primitive
    rule for reciprocal powers used in Federer 2.6.3(2), pp. 117–118 A
    continuous extension of 1/(x+c) off the integration interval may be
    chosen freely. Nonvanishing of the denominator is retained explicitly. *)
Theorem affine_reciprocal_uniform_primitive (R : realType) (U : R -> R) (a b c : R) :
  continuous U ->
  (forall x, a <= x <= b -> U x=(x+c)^-1 /\ x+c != 0) ->
  is_uniform_primitive_on (fun x => -(U x)^+2) U a b.
Proof.
move=> hU hval e he.
have [M [hM hbound]] := @continuous_positive_segment_bound R U a b hU.
pose eps := e/(2*M).
have h2M : 0 < 2*M by rewrite mulr_gt0 // ltr0n.
have heps : 0 < eps by rewrite /eps divr_gt0.
have [d [hd hcont]] := @segment_uniform_continuity R U a b eps hU heps.
exists d; split=> // s u t has hsu hut htb ht.
have hs : a <= s <= b by rewrite has /=; exact: le_trans hsu (le_trans hut htb).
have hu : a <= u <= b by rewrite (le_trans has hsu) /=; exact: le_trans hut htb.
have hT : a <= t <= b by rewrite htb andbT; exact: le_trans has (le_trans hsu hut).
have hlen : 0 <= t-s by rewrite subr_ge0; exact: le_trans hsu hut.
have hUs : `|U u-U s| <= eps.
  apply: ltW; apply: (hcont u s hu hs).
  rewrite ger0_norm; last by rewrite subr_ge0.
  have hdiff : u-s <= t-s by lra.
  exact: le_lt_trans hdiff ht.
have hUt : `|U u-U t| <= eps.
  apply: ltW; apply: (hcont u t hu hT).
  rewrite ler0_norm; last by rewrite subr_le0.
  have hdiff : -(u-t) <= t-s by lra.
  exact: le_lt_trans hdiff ht.
have hincrement : U t-U s = -(t-s)*(U t*U s).
  rewrite (hval t hT).1 (hval s hs).1.
  by field; rewrite (hval t hT).2 (hval s hs).2.
have heq : U t-U s-(-(U u)^+2)*(t-s) =
    (t-s)*(U u*(U u-U s)+U s*(U u-U t)).
  rewrite hincrement; ring.
rewrite heq normrM (ger0_norm hlen).
apply: le_trans (ler_wpM2l hlen (ler_normD _ _)) _.
have hb1 : `|U u*(U u-U s)| <= M*eps.
  rewrite normrM; apply: ler_pM=> //; try exact: normr_ge0; exact: hbound.
have hb2 : `|U s*(U u-U t)| <= M*eps.
  rewrite normrM; apply: ler_pM=> //; try exact: normr_ge0; exact: hbound.
have hsum := ler_wpM2l hlen (lerD hb1 hb2).
have hcoef : (t-s)*(M*eps+M*eps)=e*(t-s).
  rewrite /eps; by field; rewrite (gt_eqF hM).
by rewrite hcoef in hsum.
Qed.
