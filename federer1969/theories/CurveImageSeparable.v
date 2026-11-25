(** Federer (1969), 2.5.16, p. 110: im g = im G is separable. The image of g
    is the image of im s under the Lipschitzian function G, and a countable
    dense subset is obtained from the rational intervals meeting im s.
    Separability is stated as the existence of a countable subset of im g
    meeting every ball centred in im g. Neither. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import CurveVariationUP CurveArcLength CurveLipschitzFactor.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ImageSeparable.
Variable R : realType.
Variable Y : metricType R.
Variable g : R -> Y.
Hypothesis hfin : curve_locally_finite_variation g.
Local Notation s := (arc_length g).

(** Source for [curve_image_factor]: im g = im G, Federer 2.5.16,
    p. 110, where G is defined on im s. *)
Lemma curve_image_factor : range g = arc_length_factor g @` range s.
Proof.
apply/seteqP; split=> y.
- by move=> [t _ <-]; exists (s t); [exists t|exact (arc_length_factor_compose hfin t)].
- by move=> [_ [t _ <-] <-]; rewrite (arc_length_factor_compose hfin); exists t.
Qed.

(** Source for [curve_rational_point]: for a pair of rationals, a
    value of g whose arc length lies between them when there is one,
    supporting the separability of im g in Federer 2.5.16, p. 110. *)
Definition curve_rational_point (q : rat * rat) : Y :=
  if pselect (exists t, ratr q.1 < s t < ratr q.2) is left h then g (sval (cid h)) else g 0.

(** Source for [curve_image_separable]: im g is separable, Federer
    2.5.16, p. 110: the values at the rational pairs form a countable
    subset of im g meeting every ball centred in im g, because
    p[g(t), g(u)] <= |s(t) - s(u)|. *)
Theorem curve_image_separable :
  exists D : set Y, countable D /\ D `<=` range g /\
    forall y, range g y -> forall e : R, 0 < e -> exists d, D d /\ mdist y d < e.
Proof.
exists (range curve_rational_point); split; last split.
- exact: sub_countable (card_image_le _ _) (countableP _).
- move=> _ [q _ <-]; rewrite /curve_rational_point; case: pselect=> [h|_].
  + by exists (sval (cid h)).
  + by exists 0.
- move=> _ [t _ <-] e he.
  have he2 : 0 < e / 2 by rewrite divr_gt0 ?ltr0n.
  have hlt1 : s t - e / 2 < s t by rewrite ltrBlDr ltrDl.
  have hlt2 : s t < s t + e / 2 by rewrite ltrDl.
  have [q1 hq1] := rat_in_itvoo hlt1; have [q2 hq2] := rat_in_itvoo hlt2.
  move: hq1 hq2; rewrite !in_itv /= => /andP[hq1a hq1b] /andP[hq2a hq2b].
  exists (curve_rational_point (q1, q2)); split; first by exists (q1, q2).
  rewrite /curve_rational_point; case: pselect=> [h|[]]; last first.
    by exists t; rewrite /= hq1b hq2a.
  have /andP[hu1 hu2] := svalP (cid h); rewrite /= in hu1 hu2.
  apply: le_lt_trans (arc_length_distance_abs hfin t (sval (cid h))) _.
  rewrite ltr_distl; apply/andP; split.
  + rewrite ltrBlDr; apply: lt_trans hu2 _; apply: lt_trans hq2b _.
    by rewrite ltrD2l ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
  + apply: (lt_trans (y := s (sval (cid h)) + e / 2)).
      by move: hq1a; rewrite ltrBlDr=> h1; apply: lt_trans h1 _; rewrite ltrD2r.
    by rewrite ltrD2l ltr_pdivrMr ?ltr0n // ltr_pMr // ltr1n.
Qed.

End ImageSeparable.
