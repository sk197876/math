(** Federer (1969), 2.5.16, p. 109: for a map g of R into a complete metric
    space with V_a^b g < oo whenever -oo < a < b < oo, the completeness of Y
    implies the existence of the one sided limits g(x-) and g(x+), because
    p[g(t), g(u)] <= s(x-) - s(t) whenever t < u < x, and s(x) - s(x-) =
    p[g(x-), g(x)], s(x+) - s(x) = p[g(x), g(x+)]. The limits are taken
    along the one sided filters of the analysis library; completeness is the
    Cauchy filter formulation of CompleteMetricUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import ExtendedRealBoundsUP ExtendedRealBounds CompleteMetricUP RealOneSidedThresholds
  CurveVariationUP CurveArcLength.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sorted_split_filter_le]: supporting splitting of a
    nondecreasing finite sequence at a point, with the point in the
    first part, Federer 2.5.16, p. 109. *)
Lemma sorted_split_filter_le (R : realType) (s : seq R) (b : R) :
  sorted <=%O s -> s = [seq x <- s | x <= b] ++ [seq x <- s | b < x].
Proof.
elim: s=> [//|t s ih] /=; rewrite (path_sortedE le_trans)=> /andP[hall hs].
case: (leP t b)=> htb /=.
- by rewrite -(ih hs).
- have h1 : [seq x <- s | x <= b] = [::].
    apply/eqP; rewrite -[_ == _]negbK -has_filter; apply/hasPn=> x hx.
    by rewrite -ltNge; apply: lt_le_trans htb _; exact: (allP hall).
  have h2 : [seq x <- s | b < x] = s.
    by apply/all_filterP/allP=> x hx; apply: lt_le_trans htb _; exact: (allP hall).
  by rewrite h1 h2.
Qed.

Section OneSidedLimits.
Variable R : realType.
Variable Y : metricType R.
Variable g : R -> Y.
Hypothesis hfin : curve_locally_finite_variation g.
Local Notation s := (arc_length g).
Local Notation sl := (arc_length_left g).
Local Notation sr := (arc_length_right g).

(** Source for [arc_length_left_oscillation]: the estimate
    p[g(t), g(u)] <= s(x-) - s(t0) for t0 <= t < x and t0 <= u < x,
    Federer 2.5.16, p. 109, where the printed form is
    p[g(t), g(u)] <= s(x-) - s(t) for t < u < x. *)
Lemma arc_length_left_oscillation (x t0 t u : R) :
  t0 <= t -> t < x -> t0 <= u -> u < x -> mdist (g t) (g u) <= sl x - s t0.
Proof.
move=> ht0t htx ht0u hux; wlog htu : t u ht0t htx ht0u hux / t <= u.
  move=> hw; case: (leP t u)=> [htu|hut]; first exact: hw.
  by rewrite metric_sym; apply: hw=> //; exact: ltW.
apply: le_trans (arc_length_distance hfin htu) _.
apply: lerB; first exact (arc_length_le_left hfin hux).
exact (arc_length_monotone hfin ht0t).
Qed.

(** Source for [arc_length_right_oscillation]: the right hand
    counterpart p[g(t), g(u)] <= s(t0) - s(x+) for x < t <= t0 and
    x < u <= t0, Federer 2.5.16, p. 109. *)
Lemma arc_length_right_oscillation (x t0 t u : R) :
  x < t -> t <= t0 -> x < u -> u <= t0 -> mdist (g t) (g u) <= s t0 - sr x.
Proof.
move=> hxt htt0 hxu hut0; wlog htu : t u hxt htt0 hxu hut0 / t <= u.
  move=> hw; case: (leP t u)=> [htu|hut]; first exact: hw.
  by rewrite metric_sym; apply: hw=> //; exact: ltW.
apply: le_trans (arc_length_distance hfin htu) _.
apply: lerB; first exact (arc_length_monotone hfin hut0).
exact (arc_length_right_le hfin hxt).
Qed.

(** Source for [curve_left_cauchy]: the image filter of g along t
    tending to x from the left is Cauchy, the step "the completeness of
    Y implies the existence of g(x-)" in Federer 2.5.16, p. 109. *)
Lemma curve_left_cauchy (x : R) : cauchy (g @ x^'-).
Proof.
apply/cauchyP=> e he.
have [t0 ht0x ht0] := arc_length_left_adherent hfin x he.
have [ht01 ht1x] := midf_lt ht0x.
exists (g ((t0 + x) / 2)).
suff : \forall t \near x^'-, ball (g ((t0 + x) / 2)) e (g t) by [].
near=> t; rewrite ballEmdist.
apply: le_lt_trans (arc_length_left_oscillation (ltW ht01) ht1x _ _) _.
- near: t; exact (nbhs_left_ge ht0x).
- near: t; exact: nbhs_left_lt.
by rewrite ltrBlDr addrC -ltrBlDr.
Unshelve. all: end_near.
Qed.

(** Source for [curve_right_cauchy]: the image filter of g along t
    tending to x from the right is Cauchy, Federer 2.5.16, p. 109. *)
Lemma curve_right_cauchy (x : R) : cauchy (g @ x^'+).
Proof.
apply/cauchyP=> e he.
have [t0 hxt0 ht0] := arc_length_right_adherent hfin x he.
have [hxt1 ht1t0] := midf_lt hxt0.
exists (g ((x + t0) / 2)).
suff : \forall t \near x^'+, ball (g ((x + t0) / 2)) e (g t) by [].
near=> t; rewrite ballEmdist.
apply: le_lt_trans (arc_length_right_oscillation hxt1 (ltW ht1t0) _ _) _.
- near: t; exact: nbhs_right_gt.
- near: t; exact (nbhs_right_le hxt0).
by rewrite ltrBlDr addrC.
Unshelve. all: end_near.
Qed.

Hypothesis hY : is_complete_metric_space Y.

(** Source for [curve_left_limit_exists]: existence of
    g(x-) = lim g(t) as t tends to x from the left, Federer 2.5.16,
    p. 109, by completeness. *)
Theorem curve_left_limit_exists (x : R) : exists y : Y, g @ x^'- --> y.
Proof. exact: hY _ (fmap_proper_filter g (at_left_proper_filter x)) (curve_left_cauchy x). Qed.

(** Source for [curve_right_limit_exists]: existence of
    g(x+) = lim g(t) as t tends to x from the right, Federer 2.5.16,
    p. 109, by completeness. *)
Theorem curve_right_limit_exists (x : R) : exists y : Y, g @ x^'+ --> y.
Proof. exact: hY _ (fmap_proper_filter g (at_right_proper_filter x)) (curve_right_cauchy x). Qed.

(** Source for [partition_chain_sum_split_left]: supporting estimate of
    a chain sum over a sequence from u to x by the variation up to the
    last term below x and the distance from that term to g(x), used for
    s(x) - s(x-) = p[g(x-), g(x)] in Federer 2.5.16, p. 109. *)
Lemma partition_chain_sum_split_left (u x : R) (p : seq R) :
  u < x -> is_variation_partition u x p ->
  exists tm, u <= tm /\ tm < x /\
    ((chain_sum g p)%:E <= curve_variation g u tm + (mdist (g tm) (g x))%:E)%E.
Proof.
move=> hux hp; have [hsort [hn [hh hl]]] := hp.
have hbound : forall t, t \in p -> u <= t <= x by move=> t ht; exact (variation_partition_bounds hp ht).
have hu_p : u \in p by case: p hh hn hsort hl hp hbound=> [//|t p'] /= -> *; exact: mem_head.
have hx_p : x \in p.
  by rewrite -hl; case: p hn hsort hh hl hp hbound hu_p=> [//|t p'] *; exact (mem_last t p').
have [q hq] : exists q, q = [seq t <- p | t < x] by eexists.
have [r hr] : exists r, r = [seq t <- p | x <= t] by eexists.
have hsplit : p = q ++ r by rewrite hq hr; exact (sorted_split_filter x hsort).
have hqne : q <> [::].
  move=> h; have : u \in q by rewrite hq mem_filter hux hu_p.
  by rewrite h.
have hrne : r <> [::].
  move=> h; have : x \in r by rewrite hr mem_filter lexx hx_p.
  by rewrite h.
have hrx : forall t, t \in r -> t = x.
  move=> t; rewrite hr mem_filter=> /andP[hxt htp]; apply/le_anti; rewrite hxt andbT.
  by have /andP[_ ->] := hbound t htp.
have hhead_r : head 0 r = x.
  by case: r hrne hrx {hr hsplit}=> [//|t r'] _ hall /=; apply: hall; exact: mem_head.
have hchain_r : chain_sum g r = 0 by exact (chain_sum_constant g hrx).
have hhq : head u q = u.
  by move: hh; rewrite hsplit; case: q hqne {hq hsplit}=> [//|t q'] _ /= ->.
have hlq : last u q = last 0 q by case: q hqne {hq hsplit hhq}=> [//|t q'].
have hsortq : sorted <=%O q by rewrite hq; exact (sorted_filter le_trans _ hsort).
have [tm htm] : exists tm, tm = last 0 q by eexists.
have htm_q : tm \in q.
  by rewrite htm; case: q hqne {hq hsplit hhq hlq hsortq htm}=> [//|t q'] _ /=; exact: mem_last.
have htm_p : tm \in p by move: htm_q; rewrite hq mem_filter=> /andP[].
have htmx : tm < x by move: htm_q; rewrite hq mem_filter=> /andP[].
have hutm : u <= tm by have /andP[-> _] := hbound tm htm_p.
have hcat : chain_sum g p = chain_sum g q + mdist (g tm) (g x).
  by rewrite {1}hsplit (chain_sum_cat g hqne hrne) hchain_r addr0 hhead_r -htm.
have hpart : is_variation_partition u tm (rcons q tm).
  split; last split; last split.
  - rewrite -cats1; apply: sorted_cat_le=> // y z hy; rewrite inE=> /eqP->.
    by rewrite htm -hlq; exact: (sorted_le_last u hsortq hy).
  - by rewrite size_rcons ltnS lt0n size_eq0; apply/eqP.
  - by rewrite -cats1; case: q hqne hhq {hq hsplit hlq hsortq htm htm_q hcat}=> [//|t q'] _ /= ->.
  - by rewrite last_rcons.
have hq_le : ((chain_sum g q)%:E <= curve_variation g u tm)%E.
  have -> : chain_sum g q = chain_sum g (rcons q tm).
    by rewrite (chain_sum_rcons g tm hqne) -htm mdistxx addr0.
  by apply: extended_real_sup_upper; exists (rcons q tm).
exists tm; split=> //; split=> //.
by rewrite hcat EFinD; exact (leeD hq_le (lexx _)).
Qed.

(** Source for [partition_chain_sum_split_right]: supporting estimate
    of a chain sum over a sequence from x to u by the distance from
    g(x) to the first term above x and the variation from that term,
    used for s(x+) - s(x) = p[g(x), g(x+)] in Federer 2.5.16, p. 109. *)
Lemma partition_chain_sum_split_right (x u : R) (p : seq R) :
  x < u -> is_variation_partition x u p ->
  exists tm, x < tm /\ tm <= u /\
    ((chain_sum g p)%:E <= (mdist (g x) (g tm))%:E + curve_variation g tm u)%E.
Proof.
move=> hxu hp; have [hsort [hn [hh hl]]] := hp.
have hbound : forall t, t \in p -> x <= t <= u by move=> t ht; exact (variation_partition_bounds hp ht).
have hx_p : x \in p by case: p hh hn hsort hl hp hbound=> [//|t p'] /= -> *; exact: mem_head.
have hu_p : u \in p.
  by rewrite -hl; case: p hn hsort hh hl hp hbound hx_p=> [//|t p'] *; exact (mem_last t p').
have [q hq] : exists q, q = [seq t <- p | t <= x] by eexists.
have [r hr] : exists r, r = [seq t <- p | x < t] by eexists.
have hsplit : p = q ++ r by rewrite hq hr; exact (sorted_split_filter_le x hsort).
have hqne : q <> [::].
  move=> h; have : x \in q by rewrite hq mem_filter lexx hx_p.
  by rewrite h.
have hrne : r <> [::].
  move=> h; have : u \in r by rewrite hr mem_filter hxu hu_p.
  by rewrite h.
have hqx : forall t, t \in q -> t = x.
  move=> t; rewrite hq mem_filter=> /andP[htx htp]; apply/le_anti; rewrite htx.
  by have /andP[-> _] := hbound t htp.
have hlast_q : last 0 q = x.
  by case: q hqne hqx {hq hsplit}=> [//|t q'] _ hall /=; apply: hall; exact: mem_last.
have hchain_q : chain_sum g q = 0 by exact (chain_sum_constant g hqx).
have hlast_r : last 0 r = u.
  by move: hl; rewrite hsplit last_cat; case: r hrne {hr hsplit}=> [//|t r'] _ /=.
have hsortr : sorted <=%O r by rewrite hr; exact (sorted_filter le_trans _ hsort).
have [tm htm] : exists tm, tm = head 0 r by eexists.
have htm_r : tm \in r.
  by rewrite htm; case: r hrne {hr hsplit hlast_r hsortr htm}=> [//|t r'] _ /=; exact: mem_head.
have htm_p : tm \in p by move: htm_r; rewrite hr mem_filter=> /andP[].
have hxtm : x < tm by move: htm_r; rewrite hr mem_filter=> /andP[].
have htmu : tm <= u by have /andP[_ ->] := hbound tm htm_p.
have hcat : chain_sum g p = mdist (g x) (g tm) + chain_sum g r.
  by rewrite {1}hsplit (chain_sum_cat g hqne hrne) hchain_q add0r hlast_q -htm.
have hpart : is_variation_partition tm u (tm :: r).
  split; last split; last split.
  - by case: r hsortr htm {hr hsplit hlast_r htm_r hcat hrne}=> [//|t r'] hs /= ->; rewrite lexx /=; exact: hs.
  - by rewrite /= ltnS lt0n size_eq0; apply/eqP.
  - by [].
  - by rewrite /= -hlast_r; case: r hrne {hr hsplit hlast_r hsortr htm htm_r hcat}=> [//|t r'].
have hr_le : ((chain_sum g r)%:E <= curve_variation g tm u)%E.
  have -> : chain_sum g r = chain_sum g (tm :: r).
    by case: r htm hrne {hr hsplit hlast_r hsortr htm_r hcat hpart}=> [//|t r'] /= -> _; rewrite mdistxx add0r.
  by apply: extended_real_sup_upper; exists (tm :: r).
exists tm; split=> //; split=> //.
by rewrite hcat EFinD; exact (leeD (lexx _) hr_le).
Qed.

(** Source for [curve_left_jump_le]: p[g(x-), g(x)] <= s(x) - s(x-),
    half of the identity s(x) - s(x-) = p[g(x-), g(x)] in Federer
    2.5.16, p. 109, from p[g(t), g(x)] <= s(x) - s(t) for t < x. *)
Lemma curve_left_jump_le (x : R) (y : Y) : g @ x^'- --> y -> mdist y (g x) <= s x - sl x.
Proof.
move=> hy; apply/ler_addgt0Pr=> e he.
have he2 : 0 < e / 2 by rewrite divr_gt0 ?ltr0n.
have [t0 ht0x ht0] := arc_length_left_adherent hfin x he2.
have hb : \forall t \near x^'-, mdist y (g t) < e / 2.
  have hb0 : x^'- (g @^-1` ball y (e / 2)) := hy _ (nbhsx_ballx y (e / 2) he2).
  by move: hb0; apply: filterS=> t /=; rewrite ballEmdist.
have hnear : \forall t \near x^'-, t0 < t /\ t < x /\ mdist y (g t) < e / 2.
  near=> t; split; first by near: t; exact (nbhs_left_gt ht0x).
  split; first by near: t; exact: nbhs_left_lt.
  by near: t; exact: hb.
have [t [ht0t [htx hdist]]] := filter_ex hnear.
apply: le_trans (metric_triangle y (g t) (g x)) _.
have h1 : mdist (g t) (g x) <= s x - s t by exact (arc_length_distance hfin (ltW htx)).
have h2 : s t0 <= s t by exact (arc_length_monotone hfin (ltW ht0t)).
rewrite (splitr e) addrCA; apply: lerD; first exact (ltW hdist).
apply: le_trans h1 _; rewrite -addrA lerD2l lerNl opprD opprK.
exact (ltW (lt_le_trans ht0 h2)).
Unshelve. all: end_near.
Qed.

(** Source for [curve_left_jump_ge]: s(x) - s(x-) <= p[g(x-), g(x)],
    the other half of the identity in Federer 2.5.16, p. 109, by
    splitting each chain sum at its last term below x. *)
Lemma curve_left_jump_ge (x : R) (y : Y) : g @ x^'- --> y -> s x - sl x <= mdist y (g x).
Proof.
move=> hy; apply/ler_addgt0Pr=> e he.
have he2 : 0 < e / 2 by rewrite divr_gt0 ?ltr0n.
have [u1 hu1x hu1] := arc_length_left_adherent hfin x he2.
have hb : \forall t \near x^'-, mdist y (g t) < e / 2.
  have hb0 : x^'- (g @^-1` ball y (e / 2)) := hy _ (nbhsx_ballx y (e / 2) he2).
  by move: hb0; apply: filterS=> t /=; rewrite ballEmdist.
have hnear : \forall t \near x^'-, u1 < t /\ mdist y (g t) < e / 2.
  near=> t; split; first by near: t; exact (nbhs_left_gt hu1x).
  by near: t; exact: hb.
have [u0 [hu0x hu0]] := at_left_threshold hnear.
have [u [hu0u hux]] : exists u, u0 < u /\ u < x.
  by exists ((u0 + x) / 2); have [h1 h2] := midf_lt hu0x.
have [hu1u hdu] := hu0 u hu0u hux.
have hsu : sl x - e / 2 < s u.
  exact (lt_le_trans hu1 (arc_length_monotone hfin (ltW hu1u))).
have hV : (curve_variation g u x <= (mdist y (g x) + e)%:E)%E.
  apply: extended_real_sup_least=> v [p [hp ->]].
  have [tm [hutm [htmx hle]]] := partition_chain_sum_split_left hux hp.
  apply: le_trans hle _; rewrite -(arc_length_increment hfin hutm) -EFinD lee_fin.
  have h1 : s tm <= sl x by exact (arc_length_le_left hfin htmx).
  have [_ h2] := hu0 tm (lt_le_trans hu0u hutm) htmx.
  have hA : s tm - s u <= e / 2.
    apply: ltW; rewrite ltrBlDr; apply: le_lt_trans h1 _.
    by rewrite addrC -ltrBlDr.
  have hB : mdist (g tm) (g x) <= mdist y (g x) + e / 2.
    apply: le_trans (metric_triangle (g tm) y (g x)) _.
    by rewrite addrC [mdist (g tm) y]metric_sym; exact (lerD (lexx _) (ltW h2)).
  by rewrite (splitr e) [X in _ <= X]addrA [X in X <= _]addrC; exact (lerD hB hA).
apply: le_trans (lerB (lexx (s x)) (arc_length_le_left hfin hux)) _.
by rewrite -lee_fin (arc_length_increment hfin (ltW hux)).
Unshelve. all: end_near.
Qed.

(** Source for [curve_left_jump]: s(x) - s(x-) = p[g(x-), g(x)],
    Federer 2.5.16, p. 109, for any left limit g(x-) of g at x. *)
Theorem curve_left_jump (x : R) (y : Y) : g @ x^'- --> y -> s x - sl x = mdist y (g x).
Proof.
by move=> hy; apply/le_anti/andP; split; [exact: curve_left_jump_ge|exact: curve_left_jump_le].
Qed.

(** Source for [curve_right_jump_le]: p[g(x), g(x+)] <= s(x+) - s(x),
    half of the identity s(x+) - s(x) = p[g(x), g(x+)] in Federer
    2.5.16, p. 109. *)
Lemma curve_right_jump_le (x : R) (y : Y) : g @ x^'+ --> y -> mdist (g x) y <= sr x - s x.
Proof.
move=> hy; apply/ler_addgt0Pr=> e he.
have he2 : 0 < e / 2 by rewrite divr_gt0 ?ltr0n.
have [t0 hxt0 ht0] := arc_length_right_adherent hfin x he2.
have hb : \forall t \near x^'+, mdist y (g t) < e / 2.
  have hb0 : x^'+ (g @^-1` ball y (e / 2)) := hy _ (nbhsx_ballx y (e / 2) he2).
  by move: hb0; apply: filterS=> t /=; rewrite ballEmdist.
have hnear : \forall t \near x^'+, x < t /\ t < t0 /\ mdist y (g t) < e / 2.
  near=> t; split; first by near: t; exact: nbhs_right_gt.
  split; first by near: t; exact (nbhs_right_lt hxt0).
  by near: t; exact: hb.
have [t [hxt [htt0 hdist]]] := filter_ex hnear.
apply: le_trans (metric_triangle (g x) (g t) y) _.
have h1 : mdist (g x) (g t) <= s t - s x by exact (arc_length_distance hfin (ltW hxt)).
have h2 : s t <= s t0 by exact (arc_length_monotone hfin (ltW htt0)).
rewrite (splitr e) addrA; apply: lerD; last by rewrite metric_sym; exact (ltW hdist).
apply: le_trans h1 _; rewrite addrAC lerD2r.
exact (ltW (le_lt_trans h2 ht0)).
Unshelve. all: end_near.
Qed.

(** Source for [curve_right_jump_ge]: s(x+) - s(x) <= p[g(x), g(x+)],
    the other half of the identity in Federer 2.5.16, p. 109, by
    splitting each chain sum at its first term above x. *)
Lemma curve_right_jump_ge (x : R) (y : Y) : g @ x^'+ --> y -> sr x - s x <= mdist (g x) y.
Proof.
move=> hy; apply/ler_addgt0Pr=> e he.
have he2 : 0 < e / 2 by rewrite divr_gt0 ?ltr0n.
have [u1 hxu1 hu1] := arc_length_right_adherent hfin x he2.
have hb : \forall t \near x^'+, mdist y (g t) < e / 2.
  have hb0 : x^'+ (g @^-1` ball y (e / 2)) := hy _ (nbhsx_ballx y (e / 2) he2).
  by move: hb0; apply: filterS=> t /=; rewrite ballEmdist.
have hnear : \forall t \near x^'+, t < u1 /\ mdist y (g t) < e / 2.
  near=> t; split; first by near: t; exact (nbhs_right_lt hxu1).
  by near: t; exact: hb.
have [u0 [hxu0 hu0]] := at_right_threshold hnear.
have [u [hxu huu0]] : exists u, x < u /\ u < u0.
  by exists ((x + u0) / 2); have [h1 h2] := midf_lt hxu0.
have [huu1 hdu] := hu0 u hxu huu0.
have hsu : s u < sr x + e / 2.
  exact (le_lt_trans (arc_length_monotone hfin (ltW huu1)) hu1).
have hV : (curve_variation g x u <= (mdist (g x) y + e)%:E)%E.
  apply: extended_real_sup_least=> v [p [hp ->]].
  have [tm [hxtm [htmu hle]]] := partition_chain_sum_split_right hxu hp.
  apply: le_trans hle _; rewrite -(arc_length_increment hfin htmu) -EFinD lee_fin.
  have h1 : sr x <= s tm by exact (arc_length_right_le hfin hxtm).
  have [_ h2] := hu0 tm hxtm (le_lt_trans htmu huu0).
  have hA : s u - s tm <= e / 2.
    apply: ltW; rewrite ltrBlDr; apply: lt_le_trans hsu _.
    by rewrite addrC lerD2l.
  have hB : mdist (g x) (g tm) <= mdist (g x) y + e / 2.
    apply: le_trans (metric_triangle (g x) y (g tm)) _.
    exact (lerD (lexx _) (ltW h2)).
  by rewrite (splitr e) [X in _ <= X]addrA; exact (lerD hB hA).
apply: le_trans (lerB (arc_length_right_le hfin hxu) (lexx (s x))) _.
by rewrite -lee_fin (arc_length_increment hfin (ltW hxu)).
Unshelve. all: end_near.
Qed.

(** Source for [curve_right_jump]: s(x+) - s(x) = p[g(x), g(x+)],
    Federer 2.5.16, p. 109, for any right limit g(x+) of g at x. *)
Theorem curve_right_jump (x : R) (y : Y) : g @ x^'+ --> y -> sr x - s x = mdist (g x) y.
Proof.
by move=> hy; apply/le_anti/andP; split; [exact: curve_right_jump_ge|exact: curve_right_jump_le].
Qed.

End OneSidedLimits.
