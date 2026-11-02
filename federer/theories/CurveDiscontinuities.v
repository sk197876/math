(** Federer (1969), 2.5.16, p. 109: g and s have the same points of
    discontinuity, and to each point x of discontinuity corresponds the
    nonempty open interval {z : s(x-) < z < s(x+)}; since the intervals
    corresponding to distinct points are disjoint, they form a countable
    family. Continuity at x is the convergence of the function along the
    neighbourhood filter of x, split into the two one sided filters. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology normedtype.
From Federer Require Import CompleteMetricUP CurveVariationUP CurveArcLength CurveOneSidedLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Discontinuities.
Variable R : realType.
Variable Y : metricType R.
Variable g : R -> Y.
Hypothesis hfin : curve_locally_finite_variation g.
Local Notation s := (arc_length g).
Local Notation sl := (arc_length_left g).
Local Notation sr := (arc_length_right g).

(** Source for [curve_jump_points]: the points x of discontinuity of
    s, those with s(x-) < s(x+), Federer 2.5.16, p. 109. *)
Definition curve_jump_points : set R := [set x | sl x < sr x].

(** Source for [arc_length_left_continuous_iff]: s is continuous from
    the left at x exactly when s(x-) = s(x), Federer 2.5.16, p. 109,
    where s(x-) = lim s(t) as t tends to x from the left. *)
Lemma arc_length_left_continuous_iff (x : R) : s @ x^'- --> s x <-> sl x = s x.
Proof.
split=> [hc|hl].
- apply/le_anti; rewrite (arc_length_left_le hfin x) /=.
  apply/ler_addgt0Pr=> e he.
  have hb : \forall t \near x^'-, ball (s x) e (s t) by exact ((cvg_ballP _ _).1 hc e he).
  have hnear : \forall t \near x^'-, t < x /\ ball (s x) e (s t).
    by near=> t; split; [near: t; exact: nbhs_left_lt|near: t; exact: hb].
  have [t [htx hball]] := filter_ex hnear.
  move: hball; rewrite /ball /= ltr_norml=> /andP[_ h].
  rewrite ltrBlDr in h; apply: le_trans (ltW h) _.
  by rewrite addrC lerD2r; exact (arc_length_le_left hfin htx).
- apply/cvg_ballP=> e he.
  have [t0 ht0x ht0] := arc_length_left_adherent hfin x he.
  near=> t; rewrite /ball /= ltr_norml; apply/andP; split.
  + apply: (lt_le_trans (y := 0)); first by rewrite oppr_lt0.
    rewrite subr_ge0; apply: (arc_length_monotone hfin).
    by near: t; exact: nbhs_left_le.
  + rewrite -hl ltrBlDr addrC -ltrBlDr; apply: lt_le_trans ht0 _.
    apply: (arc_length_monotone hfin).
    by near: t; exact: nbhs_left_ge ht0x.
Unshelve. all: end_near.
Qed.

(** Source for [arc_length_right_continuous_iff]: s is continuous from
    the right at x exactly when s(x+) = s(x), Federer 2.5.16, p. 109. *)
Lemma arc_length_right_continuous_iff (x : R) : s @ x^'+ --> s x <-> sr x = s x.
Proof.
split=> [hc|hr].
- apply/le_anti; rewrite (arc_length_right_ge hfin x) andbT.
  apply/ler_addgt0Pr=> e he.
  have hb : \forall t \near x^'+, ball (s x) e (s t) by exact ((cvg_ballP _ _).1 hc e he).
  have hnear : \forall t \near x^'+, x < t /\ ball (s x) e (s t).
    by near=> t; split; [near: t; exact: nbhs_right_gt|near: t; exact: hb].
  have [t [hxt hball]] := filter_ex hnear.
  move: hball; rewrite /ball /= ltr_norml=> /andP[h _].
  apply: le_trans (arc_length_right_le hfin hxt) _.
  by move: h; rewrite ltrBrDr addrC ltrBlDr=> /ltW.
- apply/cvg_ballP=> e he.
  have [t0 hxt0 ht0] := arc_length_right_adherent hfin x he.
  near=> t; rewrite /ball /= ltr_norml; apply/andP; split.
  + rewrite ltrBrDr addrC ltrBlDr -hr.
    apply: le_lt_trans (arc_length_monotone hfin _) ht0.
    by near: t; exact: nbhs_right_le hxt0.
  + apply: (le_lt_trans (y := 0)); last exact: he.
    rewrite subr_le0; apply: (arc_length_monotone hfin).
    by near: t; exact: nbhs_right_ge.
Unshelve. all: end_near.
Qed.

Hypothesis hY : is_complete_metric_space Y.

(** Source for [curve_left_continuous_iff]: g is continuous from the
    left at x exactly when s(x-) = s(x), Federer 2.5.16, p. 109, by
    s(x) - s(x-) = p[g(x-), g(x)] and the existence of g(x-). *)
Lemma curve_left_continuous_iff (x : R) : g @ x^'- --> g x <-> sl x = s x.
Proof.
split=> [hc|hl].
- have := curve_left_jump hfin hc; rewrite mdistxx=> /eqP; rewrite subr_eq0=> /eqP h.
  by rewrite h.
- have [y hy] := curve_left_limit_exists hfin hY x.
  suff -> : g x = y by [].
  apply: mdist_positivity; have := curve_left_jump hfin hy.
  by rewrite hl subrr metric_sym=> h; rewrite -h.
Qed.

(** Source for [curve_right_continuous_iff]: g is continuous from the
    right at x exactly when s(x+) = s(x), Federer 2.5.16, p. 109, by
    s(x+) - s(x) = p[g(x), g(x+)] and the existence of g(x+). *)
Lemma curve_right_continuous_iff (x : R) : g @ x^'+ --> g x <-> sr x = s x.
Proof.
split=> [hc|hr].
- have := curve_right_jump hfin hc; rewrite mdistxx=> /eqP; rewrite subr_eq0=> /eqP h.
  by rewrite h.
- have [y hy] := curve_right_limit_exists hfin hY x.
  suff -> : g x = y by [].
  apply: mdist_positivity; have := curve_right_jump hfin hy.
  by rewrite hr subrr=> h; rewrite -h.
Qed.

(** Source for [curve_continuous_iff]: g and s have the same points of
    discontinuity, Federer 2.5.16, p. 109: g is continuous at x exactly
    when s is continuous at x. *)
Theorem curve_continuous_iff (x : R) : g @ x --> g x <-> s @ x --> s x.
Proof.
split=> h.
- have [hl hr] := (left_right_continuousP g x).2 h.
  apply/left_right_continuousP; split.
  + exact/arc_length_left_continuous_iff/curve_left_continuous_iff.
  + exact/arc_length_right_continuous_iff/curve_right_continuous_iff.
- have [hl hr] := (left_right_continuousP s x).2 h.
  apply/left_right_continuousP; split.
  + exact/curve_left_continuous_iff/arc_length_left_continuous_iff.
  + exact/curve_right_continuous_iff/arc_length_right_continuous_iff.
Qed.

(** Source for [curve_jump_points_iff]: the points of discontinuity of
    g are the points x with s(x-) < s(x+), Federer 2.5.16, p. 109. *)
Theorem curve_jump_points_iff (x : R) : curve_jump_points x <-> ~ (g @ x --> g x).
Proof.
rewrite /curve_jump_points /=; split=> [hlt hc|hn].
- have [hl hr] := (left_right_continuousP g x).2 hc.
  move: hlt; rewrite (curve_left_continuous_iff _).1 // (curve_right_continuous_iff _).1 //.
  by rewrite ltxx.
- rewrite lt_neqAle arc_length_left_le_right ?andbT //; apply/eqP=> heq; apply: hn.
  apply/left_right_continuousP; split.
  + apply/curve_left_continuous_iff; apply/le_anti; rewrite (arc_length_left_le hfin x) /=.
    by rewrite heq; exact: arc_length_right_ge.
  + apply/curve_right_continuous_iff; apply/le_anti; rewrite (arc_length_right_ge hfin x) andbT.
    by rewrite -heq; exact: arc_length_left_le.
Qed.

(** Source for [curve_jump_points_separated]: the intervals
    {z : s(x-) < z < s(x+)} corresponding to distinct points of
    discontinuity are disjoint, Federer 2.5.16, p. 109: for x < y,
    s(x+) <= s(y-). *)
Lemma curve_jump_points_separated (x y : R) : x < y -> sr x <= sl y.
Proof.
move=> hxy; have [h1 h2] := midf_lt hxy.
exact: le_trans (arc_length_right_le hfin h1) (arc_length_le_left hfin h2).
Qed.

(** Source for [curve_jump_rational]: a rational number in the interval
    {z : s(x-) < z < s(x+)} of a point x of discontinuity, Federer
    2.5.16, p. 109, supporting the countability of the family. *)
Definition curve_jump_rational (x : R) : rat :=
  if pselect (sl x < sr x) is left h then sval (cid (rat_in_itvoo h)) else 0.

(** Source for [curve_jump_rational_in]: the chosen rational lies in
    the interval, Federer 2.5.16, p. 109. *)
Lemma curve_jump_rational_in (x : R) :
  sl x < sr x -> sl x < ratr (curve_jump_rational x) < sr x.
Proof.
move=> h; rewrite /curve_jump_rational; case: pselect=> [h'|//].
by have := svalP (cid (rat_in_itvoo h')); rewrite in_itv.
Qed.

(** Source for [curve_jump_points_countable]: the points of
    discontinuity form a countable family, Federer 2.5.16, p. 109. *)
Theorem curve_jump_points_countable : countable curve_jump_points.
Proof.
apply/countable_injP; exists (fun x => pickle (curve_jump_rational x)).
move=> x y /set_mem hx /set_mem hy /(pcan_inj pickleK) hq.
case: (ltgtP x y)=> // hxy.
- have /andP[_ h1] := curve_jump_rational_in hx.
  have /andP[h2 _] := curve_jump_rational_in hy.
  by have := lt_trans (lt_le_trans h1 (curve_jump_points_separated hxy)) h2; rewrite hq ltxx.
- have /andP[_ h1] := curve_jump_rational_in hy.
  have /andP[h2 _] := curve_jump_rational_in hx.
  by have := lt_trans (lt_le_trans h1 (curve_jump_points_separated hxy)) h2; rewrite hq ltxx.
Qed.

End Discontinuities.
