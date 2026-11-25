(** Consequences of the definitions in Federer (1969), 2.8.1, pp. 141–142.
    The proof rules below keep the ambient measure and closed-family
    hypotheses separate from fineness and adequacy. edition details and the
    difference in standing hypotheses are recorded in CoveringFamilyUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureAlmostBasic CountablyClosedFamilyUP MetricClosedBalls
  MetricDiameterUP MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_open_ball_open]: supporting topology
    of U(a,r) in Federer 2.8.1, p. 141. Openness follows
    from the metric triangle inequality, already proved for
    this precise distance set in MetricClosedBalls.v. *)
Lemma covering_open_ball_open (R : realType) (X : metricType R)
    (a : X) (r : R) : open (metric_open_ball a r).
Proof. exact: metric_open_ball_open. Qed.

(** Source for [covering_open_ball_center]: the center belongs
    to a positive-radius ball, supporting fine coverings in
    Federer 2.8.1, pp. 141–142. *)
Lemma covering_open_ball_center (R : realType) (X : metricType R)
    (a : X) (r : R) : (0 < r)%R -> metric_open_ball a r a.
Proof. by rewrite /metric_open_ball /= mdistxx. Qed.

(** Source for [covering_open_ball_mono]: supporting nesting
    of U(a,r) from Federer 2.8.1, p. 141. *)
Lemma covering_open_ball_mono (R : realType) (X : metricType R)
    (a : X) (r s : R) : (r <= s)%R ->
  metric_open_ball a r `<=` metric_open_ball a s.
Proof. by move=> hrs x hx; exact: lt_le_trans hx hrs. Qed.

(** Source for [covering_closed_ball_bounded]: supporting
    boundedness of B(a,r) in Federer 2.8.1, p. 141;
    its diameter is at most 2r for nonnegative r. *)
Lemma covering_closed_ball_bounded (R : realType) (X : metricType R)
    (a : X) (r : R) : (0 <= r)%R ->
  metric_set_bounded (metric_closed_ball a r).
Proof.
move=> hr; apply: (le_lt_trans _ (ltry (r+r)%R)).
apply: (metric_diameter_least
  (extended_metric_diameter_specification (metric_closed_ball a r))).
- by rewrite lee_fin; apply: addr_ge0.
- move=> x y hx hy; rewrite lee_fin.
  exact: metric_closed_ball_diameter_bound hx hy.
Qed.

(** Source for [covering_context_member_measurable]: the
    members of F are measurable under the standing hypotheses
    of Federer 2.8.1, p. 141. This is used explicitly
    in the finite-subfamily argument of 2.8.2, p. 143. *)
Lemma covering_context_member_measurable (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R) :
  is_covering_theory_context F mu ->
  forall B, F B -> measure_measurable mu B.
Proof.
move=> hc B hB.
have h := measure_measurable_complement
  (covering_context_open_measurable hc (closed_openC (covering_context_closed hc hB))).
by rewrite setCK in h.
Qed.

(** Source for [covering_context_ball_finite]: positive balls
    have finite measure under Federer 2.8.1, p. 141.
    No compactness of the ball or separability of X is used. *)
Lemma covering_context_ball_finite (R : realType) (X : metricType R)
    (F : set (set X)) (mu : set X -> \bar R)
    (hc : is_covering_theory_context F mu) (a : X) (r : R) :
  (0 <= r)%R -> mu (metric_open_ball a r) < +oo.
Proof.
move=> hr.
have hsub : metric_open_ball a r `<=` metric_closed_ball a r.
  move=> x hx; exact: ltW hx.
apply: le_lt_trans (@measure_mono R X mu (covering_context_measure hc)
  (metric_open_ball a r) (metric_closed_ball a r) hsub) _.
exact (@covering_context_bounded_finite R X F mu hc (metric_closed_ball a r)
  (@covering_closed_ball_bounded R X a r hr)).
Qed.

(** Source for [fine_cover_mono_set]: supporting restriction
    of the target in the definition of Federer 2.8.1, p. 142;
    no measurability of the target is required. *)
Lemma fine_cover_mono_set (R : realType) (X : metricType R)
    (F : set (set X)) (A B : set X) :
  A `<=` B -> family_covers_finely F B -> family_covers_finely F A.
Proof. by move=> hAB hf a ha; exact: hf a (hAB a ha). Qed.

(** Source for [fine_cover_mono_family]: enlarging a fine
    family preserves fineness, directly from Federer 2.8.1,
    p. 142, first paragraph. *)
Lemma fine_cover_mono_family (R : realType) (X : metricType R)
    (F H : set (set X)) (A : set X) :
  F `<=` H -> family_covers_finely F A -> family_covers_finely H A.
Proof.
move=> hFH hf a ha e he; have [B [hB [hb hsub]]] := hf a ha e he.
exists B; split; first exact: hFH B hB.
by split.
Qed.

(** Source for [fine_cover_empty_target]: empty-target boundary
    of the fine-cover definition, Federer 2.8.1, p. 142. *)
Lemma fine_cover_empty_target (R : realType) (X : metricType R)
    (F : set (set X)) : family_covers_finely F set0.
Proof. by move=> a []. Qed.

(** Source for [fine_cover_empty_family]: the empty family
    covers A finely exactly when A is empty, a boundary
    consequence of Federer 2.8.1, p. 142. *)
Lemma fine_cover_empty_family (R : realType) (X : metricType R)
    (A : set X) : family_covers_finely set0 A <-> A = set0.
Proof.
split.
- move=> hf; apply/seteqP; split=> [a ha|a []].
  have [B [hB _]] := hf a ha 1%R (ltr01 : (0 < 1)%R).
  exact hB.
- move=> ->; exact: fine_cover_empty_target.
Qed.

(** Source for [adequate_selection_mono_set]: a selection
    adequate for B is adequate for A contained in B, by
    null-set monotonicity in Federer 2.8.1, p. 142. *)
Lemma adequate_selection_mono_set (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A B V : set X) (G : set (set X)) :
  A `<=` B -> is_adequate_cover_selection mu F B V G ->
  is_adequate_cover_selection mu F A V G.
Proof.
move=> hAB hG; constructor.
- exact: adequate_selection_members hG.
- exact: adequate_selection_countable hG.
- exact: adequate_selection_disjoint hG.
- exact: adequate_selection_within hG.
- apply: (@measure_null_subset R X mu hm _ _ _ (adequate_selection_remainder hG)).
  by move=> x [[hv ha] hn]; split=> //; split=> //; exact: hAB.
Qed.

(** Source for [adequate_family_mono_set]: downward closure
    in the target of adequacy from Federer 2.8.1, p. 142;
    this needs only the outer-measure laws. *)
Lemma adequate_family_mono_set (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A B : set X) :
  A `<=` B -> family_is_measure_adequate mu F B ->
  family_is_measure_adequate mu F A.
Proof.
move=> hAB hf V hV; have [G hG] := hf V hV.
exists G; exact (@adequate_selection_mono_set R X mu hm F A B V G hAB hG).
Qed.

(** Source for [adequate_family_mono_family]: enlarging the eligible family
    preserves adequacy, Federer 2.8.1, p. 142 Closedness is a separate
    standing hypothesis and is unnecessary for this implication. *)
Lemma adequate_family_mono_family (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (F H : set (set X)) (A : set X) :
  F `<=` H -> family_is_measure_adequate mu F A ->
  family_is_measure_adequate mu H A.
Proof.
move=> hFH hf V hV; have [G hG] := hf V hV; exists G; constructor.
- move=> B hB; exact: hFH _ (adequate_selection_members hG hB).
- exact: adequate_selection_countable hG.
- exact: adequate_selection_disjoint hG.
- exact: adequate_selection_within hG.
- exact: adequate_selection_remainder hG.
Qed.

(** Source for [adequate_family_null_target]: any family is
    adequate for a null target, by choosing the empty subfamily
    in Federer 2.8.1, p. 142. This includes empty ambient spaces. *)
Lemma adequate_family_null_target (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : set (set X)) (A : set X) :
  mu A = 0 -> family_is_measure_adequate mu F A.
Proof.
move=> hA V hV; exists set0; constructor.
- by move=> B [].
- exact: countable0.
- by move=> B C [].
- by move=> x [B []].
- have he : ((V `&` A) `\` \bigcup_(B in (@set0 (set X))) B) = V `&` A.
    apply/seteqP; split=> [x [hx _]|x hx]; first exact hx.
    split=> //; by move=> [B []].
  rewrite he; apply: (@measure_null_subset R X mu hm _ A _ hA).
  by move=> x [].
Qed.

(** Source for [adequate_family_empty_target]: the empty
    target is adequate, supporting the boundary cases of
    Federer 2.8.1, p. 142. *)
Lemma adequate_family_empty_target (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (F : set (set X)) :
  family_is_measure_adequate mu F set0.
Proof. exact (@adequate_family_null_target R X mu hm F set0 (measure_empty hm)). Qed.
