(** Supporting the discontinuous-curve formula in Federer (1969), 2.10.14,
    p. 177: a one-sided jump vanishes exactly when the curve is continuous
    from that side. Local changes outside the corresponding one-sided
    neighbourhood do not affect it. These facts concern the printed distance
    upper limits even when one-sided limits in the target do not exist. The
    relevant upper-integral correction is erratum p. 3, book p. 177 line 23,
    not a correction to the jump definitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype lra.
From Federer Require Import ExtendedRealBounds CurveOneSidedJumpUP RealOneSidedThresholds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_jump_near_upper_bound]: supporting filter form
    of an eventual upper bound for alpha_+ or alpha_- in
    2.10.14, p. 177. Neighbourhood thresholds are general
    topology of R, with no variation hypothesis. *)
Lemma curve_jump_near_upper_bound (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) (b : \bar R) :
  (if right then (\forall t \near x^'+, (mdist (g t) (g x))%:E<=b)
    else (\forall t \near x^'-, (mdist (g t) (g x))%:E<=b)) ->
  curve_one_sided_jump g right x<=b.
Proof.
case: right=> hn; apply: curve_one_sided_jump_upper_bound.
- have [u [hxu hu]] := at_right_threshold hn.
  exists (u-x)%R; split; first by rewrite subr_gt0.
  move=> t; rewrite /curve_side_offset /= => /andP[hxt htu].
  apply: hu; lra.
- have [u [hux hu]] := at_left_threshold hn.
  exists (x-u)%R; split; first by rewrite subr_gt0.
  move=> t; rewrite /curve_side_offset /= => /andP[htx hut].
  apply: hu; lra.
Qed.

(** Source for [curve_continuous_one_sided_jump_zero]: supporting
    zero-jump consequence of continuity in 2.10.14, p. 177.
    This identifies the continuous special case with 2.10.13
    and does not require a complete metric target. *)
Lemma curve_continuous_one_sided_jump_zero (R : realType) (Y : metricType R)
    (g : R -> Y) (right : bool) (x : R) : g @ x --> g x ->
  curve_one_sided_jump g right x=0.
Proof.
move=> hc; apply/eqP; rewrite eq_le curve_one_sided_jump_nonnegative andbT.
apply/lee_addgt0Pr=> e he; rewrite add0e.
have hb : \forall t \near x, (mdist (g t) (g x))%:E<=e%:E.
  have hh : nbhs x (g @^-1` ball (g x) e) := hc _ (nbhsx_ballx (g x) e he).
  move: hh; apply: filterS=> t ht; move: ht; rewrite ballEmdist metric_sym=> h.
  by rewrite lee_fin; exact: ltW h.
apply: curve_jump_near_upper_bound.
case: right=> /=; rewrite near_withinE;
  apply: (filterS _ hb)=> t ht hside; exact ht.
Qed.

(** Source for [curve_right_jump_zero_continuous]: supporting
    right-hand criterion for alpha_+=0 in 2.10.14, p. 177.
    The infimum approximation yields the usual one-sided metric
    epsilon law; no right limit is assumed in advance. *)
Lemma curve_right_jump_zero_continuous (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_right_jump_size g x=0 -> g @ x^'+ --> g x.
Proof.
move=> hz; apply/cvg_ballP=> e he.
have hlt : curve_one_sided_jump g true x<e%:E by rewrite -/(curve_right_jump_size g x) hz lte_fin.
have [d [hd hb]] := curve_one_sided_jump_strict_bound hlt.
near=> t; rewrite ballEmdist /= metric_sym.
have hxt : (x<t)%R by near: t; exact: nbhs_right_gt.
have htd : (t<x+d)%R by near: t; apply: nbhs_right_lt; lra.
have ht : (0<curve_side_offset true x t<d)%R.
  rewrite /curve_side_offset /=; apply/andP; split; lra.
by have hh := hb t ht; rewrite lte_fin in hh.
Unshelve. all: end_near.
Qed.

(** Source for [curve_left_jump_zero_continuous]: supporting
    left-hand criterion for alpha_-=0 in 2.10.14, p. 177.
    The point x itself is omitted from the left neighbourhood. *)
Lemma curve_left_jump_zero_continuous (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_left_jump_size g x=0 -> g @ x^'- --> g x.
Proof.
move=> hz; apply/cvg_ballP=> e he.
have hlt : curve_one_sided_jump g false x<e%:E by rewrite -/(curve_left_jump_size g x) hz lte_fin.
have [d [hd hb]] := curve_one_sided_jump_strict_bound hlt.
near=> t; rewrite ballEmdist /= metric_sym.
have htx : (t<x)%R by near: t; exact: nbhs_left_lt.
have hdt : (x-d<t)%R by near: t; apply: nbhs_left_gt; lra.
have ht : (0<curve_side_offset false x t<d)%R.
  rewrite /curve_side_offset /=; apply/andP; split; lra.
by have hh := hb t ht; rewrite lte_fin in hh.
Unshelve. all: end_near.
Qed.

(** Source for [curve_jump_zero_continuous_iff]: supporting
    continuity criterion in 2.10.14, p. 177: both nonnegative
    one-sided jumps vanish exactly at a continuity point.
    This extends the locally BV criterion of 2.5.16, p. 109,
    to arbitrary metric curves by the printed upper limits. *)
Theorem curve_jump_zero_continuous_iff (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) :
  (curve_right_jump_size g x=0 /\ curve_left_jump_size g x=0) <-> g @ x --> g x.
Proof.
split.
- move=> [hr hl]; apply/left_right_continuousP; split.
  + exact: curve_left_jump_zero_continuous hl.
  + exact: curve_right_jump_zero_continuous hr.
- move=> hc; split; exact: curve_continuous_one_sided_jump_zero hc.
Qed.

(** Source for [curve_one_sided_jump_local_equal]: supporting
    locality of alpha_+ and alpha_- in 2.10.14, p. 177.
    Agreement at x and throughout one short one-sided interval
    preserves every eventual upper bound and hence the jump. *)
Lemma curve_one_sided_jump_local_equal (R : realType) (Y : metricType R)
    (g h : R -> Y) (right : bool) (x d : R) : (0<d)%R ->
  (forall t, (0<=curve_side_offset right x t<d)%R -> g t=h t) ->
  curve_one_sided_jump g right x=curve_one_sided_jump h right x.
Proof.
move=> hd he.
have hcenter : g x=h x.
  apply: he; by rewrite /curve_side_offset subrr; case: right; rewrite /= lexx hd.
have hbound (u v : R -> Y) :
    (forall t, (0<=curve_side_offset right x t<d)%R -> u t=v t) ->
    u x=v x -> forall b, curve_side_distance_upper_bound u right x b ->
    curve_side_distance_upper_bound v right x b.
  move=> huv hx b [e [hepos hb]].
  exists (Order.min d e); split; first by rewrite lt_min hd hepos.
  move=> t /andP[ht0 htde].
  have hminD : (Order.min d e<=d)%R by rewrite ge_min lexx.
  have hminE : (Order.min d e<=e)%R by rewrite ge_min lexx orbT.
  have htd : (curve_side_offset right x t<d)%R := lt_le_trans htde hminD.
  have hte : (curve_side_offset right x t<e)%R := lt_le_trans htde hminE.
  rewrite -(huv t ltac:(by rewrite (ltW ht0) htd)) -hx.
  apply: hb; by rewrite ht0 hte.
apply/le_anti/andP; split; apply: extended_real_inf_greatest=> b hb;
  apply: curve_one_sided_jump_upper_bound.
- exact: (@hbound h g (fun t ht => esym (he t ht)) (esym hcenter) b hb).
- exact: (@hbound g h he hcenter b hb).
Qed.
