(** Federer (1969), 2.10.28(4), pp. 192–193: the constant-three estimate for
    a test interval of length at least the spacing. Count its intersected
    child indices using their first and last elements. This avoids choosing
    the book's integer k while proving the same bound. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals ring lra.
From Federer Require Import ConcaveIntervalGaugeUP ConcaveIntervalGaugeLaws
  FiniteOrdinalSpan IntervalClipLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [equal_spacing_clipped_cost_bound]: supporting
    zero cost outside intersected indices and
    cost at most h(s) inside, in the
    constant-three proof of 2.10.28(4), p. 193.
    Endpoint contacts are allowed in the index set
    and contribute zero clipped length. *)
Lemma equal_spacing_clipped_cost_bound (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (a s t u v i : R) : 0<=s ->
  h (real_interval_clip_length u v (a+i*t) (a+i*t+s))<=
    if (a+i*t<=v) && (u<=a+i*t+s) then h s else 0.
Proof.
move=> hs; case: ifP=> hmeet.
- apply: (@interval_gauge_increasing R h hg); first by rewrite /real_interval_clip_length le_max lexx.
  rewrite /real_interval_clip_length ge_max hs /=.
  have hmin : Order.min v (a+i*t+s)<=a+i*t+s by rewrite ge_min lexx orbT.
  have hmax : a+i*t<=Order.max u (a+i*t) by rewrite le_max lexx orbT.
  lra.
- have hno : ~~ ((a+i*t<=v) && (u<=a+i*t+s)) by rewrite hmeet.
  move: hno; rewrite negb_and -!ltNge=> /orP[hv|hu].
  + by rewrite (@interval_clip_length_right_zero R u v (a+i*t) (a+i*t+s) (ltW hv)) (interval_gauge_zero hg).
  + by rewrite (@interval_clip_length_left_zero R u v (a+i*t) (a+i*t+s) (ltW hu)) (interval_gauge_zero hg).
Qed.

(** Source for [equal_spacing_intersected_count_bound]: supporting
    count of child intervals meeting T in
    2.10.28(4), p. 193. If p is their
    number and L>=t, then p*t<=3L.
    The empty index set is included. *)
Lemma equal_spacing_intersected_count_bound (R : realType) n (a s t u v : R) :
  0<s -> s<t -> t<=v-u ->
  ((#|[pred i : 'I_n | (a+i%:R*t<=v) && (u<=a+i%:R*t+s)]|)%:R*t<=3*(v-u) :> R).
Proof.
move=> hs hst hL.
pose P (i : 'I_n) := (a+i%:R*t<=v) && (u<=a+i%:R*t+s).
change ((#|P|)%:R*t<=3*(v-u)).
have ht : 0<t by lra.
case: (pselect (exists i, P i))=> [hP|hno]; last first.
  have hp0 : P=1 pred0.
    move=> i; apply/negP=> hi; apply: hno; by exists i.
  have hcard : #|P|=0%N by rewrite (eq_card hp0) card0.
  rewrite hcard mul0r; lra.
have [lo [hi [hlo [hhi hspan]]]] := @finite_ordinal_extremes n P hP.
have hlohi : (lo<=hi)%N := (hspan hi hhi).1.
have /andP[hleft _] : (a+lo%:R*t<=v) && (u<=a+lo%:R*t+s) := hlo.
have /andP[_ hright] : (a+lo%:R*t<=v) && (u<=a+lo%:R*t+s) := hlo.
have /andP[hhiLeft _] : (a+hi%:R*t<=v) && (u<=a+hi%:R*t+s) := hhi.
have hcard := @finite_ordinal_span_card n P (val lo) (val hi) hspan.
have hcardR : ((#|P|)%:R<=((val hi-val lo+1)%N)%:R :> R) by rewrite ler_nat.
rewrite natrD (@natrB R (val hi) (val lo) hlohi) in hcardR.
have hmul := ler_wpM2r (ltW ht) hcardR.
lra.
Qed.

(** Source for [equal_spacing_count_cost_ratio]: supporting
    final scalar comparison to 3*zeta(J)*L/d
    in 2.10.28(4), p. 193. The
    hypotheses d<=n*t and p*t<=3L
    replace the book's floor-index calculation. *)
Lemma equal_spacing_count_cost_ratio (R : realType) (p d N t L c : R) :
  0<=p -> 0<d -> 0<N -> 0<=c -> d<=N*t -> p*t<=3*L ->
  p*(c/N)<=3*c*L/d.
Proof.
move=> hp hd hN hc hdNt hpt.
have hpd := ler_wpM2l hp hdNt.
have hptN := ler_wpM2r (ltW hN) hpt.
have hratio : p/N<=3*L/d.
  rewrite ler_pdivlMr // -mulrAC ler_pdivrMr //; lra.
have hh := ler_wpM2r hc hratio.
have he1 : p*(c/N)=(p/N)*c by ring.
have he2 : (3*L/d)*c=3*c*L/d by ring.
by rewrite he1 -he2.
Qed.
