(** Federer (1969), 3.1.13, p. 224:
    order, positivity, and Lipschitz properties
    of the truncated complement distance.
    All proofs use only the abstract infimum laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology lra.
From Federer Require Import TruncatedComplementDistanceUP MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TruncatedLaws.
Variable R : realType.
Variable X : metricType R.
Variable T : set X.
Variable d : X->R.
Hypothesis hd : is_truncated_complement_distance T d.

(** Source for [truncated_complement_distance_nonnegative]:
    zero is a lower bound of all distances
    and of the cap one in Federer
    3.1.13, p. 224. *)
Lemma truncated_complement_distance_nonnegative x : 0<=d x.
Proof.
apply: (truncated_complement_distance_greatest hd ler01).
by move=>y hy; exact: mdist_ge0.
Qed.

(** Source for [truncated_complement_distance_unique]:
    the infimum specification uniquely determines
    the truncated distance used in Federer
    3.1.13, p. 224. *)
Lemma truncated_complement_distance_unique e :
  is_truncated_complement_distance T e -> forall x, d x=e x.
Proof.
move=>he x; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (truncated_complement_distance_greatest he
    (truncated_complement_distance_cap hd x)).
  move=>y hy; exact: (truncated_complement_distance_lower hd x hy).
- apply: (truncated_complement_distance_greatest hd
    (truncated_complement_distance_cap he x)).
  move=>y hy; exact: (truncated_complement_distance_lower he x hy).
Qed.

(** Source for [truncated_complement_distance_outside]:
    the truncated distance vanishes outside
    the cover member, supporting Federer
    3.1.13, p. 224. *)
Lemma truncated_complement_distance_outside x : ~T x -> d x=0.
Proof.
move=>hx; apply/eqP; rewrite eq_le (truncated_complement_distance_nonnegative x) andbT.
have hb := truncated_complement_distance_lower hd x hx.
by rewrite mdistxx in hb.
Qed.

(** Source for [truncated_complement_distance_subtract]:
    one-sided distance variation is bounded
    by the distance between the base points,
    supporting the Lipschitz radius in Federer
    3.1.13, p. 224. *)
Lemma truncated_complement_distance_subtract x y : d x-d y<=mdist x y.
Proof.
rewrite lerBlDr addrC -lerBlDr.
apply: (truncated_complement_distance_greatest hd _).
- have hc := truncated_complement_distance_cap hd x.
  have hn := mdist_ge0 x y; lra.
- move=>z hz; rewrite lerBlDl.
  apply: (le_trans (truncated_complement_distance_lower hd x hz)).
  exact: metric_triangle.
Qed.

(** Source for [truncated_complement_distance_lipschitz]:
    each capped complement-distance function has
    Lipschitz constant at most one, supporting
    the choice of h in Federer
    3.1.13, p. 224. *)
Lemma truncated_complement_distance_lipschitz x y : `|d x-d y|<=mdist x y.
Proof.
rewrite ler_norml; apply/andP; split.
- rewrite lerNl opprB (metric_sym x y).
  exact: truncated_complement_distance_subtract.
- exact: truncated_complement_distance_subtract.
Qed.

(** Source for [truncated_complement_distance_positive]:
    an interior point of a cover member
    has positive truncated distance, as
    required for h in Federer 3.1.13, p. 224. *)
Lemma truncated_complement_distance_positive x : open T -> T x -> 0<d x.
Proof.
move=>hT hx.
have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP x T) (open_nbhs_nbhs (conj hT hx)).
have hp : 0<Num.min 1 r by rewrite lt_min ltr01 hr.
apply: (lt_le_trans hp).
apply: (truncated_complement_distance_greatest hd _).
- by rewrite ge_min lexx.
- move=>y hy.
  have hyr : r<=mdist x y.
    rewrite leNgt; apply/negP=>hh; exact: (hy (hb y hh)).
  apply: (le_trans _ hyr); by rewrite ge_min lexx orbT.
Qed.

(** Source for [truncated_complement_distance_ball_subset]:
    a ball whose radius is smaller than
    the truncated distance lies in the
    cover member, supporting subordination in
    Federer 3.1.13, pp. 224–225. *)
Lemma truncated_complement_distance_ball_subset x y :
  mdist x y<d x -> T y.
Proof.
move=>hxy; apply: contrapT=>hy.
have hh := le_lt_trans (truncated_complement_distance_lower hd x hy) hxy.
by rewrite ltxx in hh.
Qed.

(** Source for [truncated_complement_distance_minimum]:
    for a nonempty complement the abstract
    value equals min(1,dist(x,X\T)), exactly
    the term in Federer 3.1.13, p. 224. *)
Lemma truncated_complement_distance_minimum q :
  is_metric_set_distance (~` T) q ->
  forall x, d x=Num.min 1 (q x).
Proof.
move=>hq x; apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite le_min (truncated_complement_distance_cap hd x) /=.
  apply: (metric_set_distance_greatest hq).
  move=>y hy; exact: (truncated_complement_distance_lower hd x hy).
- apply: (truncated_complement_distance_greatest hd _).
  + by rewrite ge_min lexx.
  + move=>y hy.
    apply: (le_trans _ (metric_set_distance_lower hq x hy)).
    by rewrite ge_min lexx orbT.
Qed.
End TruncatedLaws.

(** Source for [truncated_complement_distance_whole]:
    a whole-space cover member contributes one
    to the supremum in Federer 3.1.13,
    p. 224. This is the capped
    empty-complement convention, without assigning
    a finite uncapped distance to the empty set. *)
Lemma truncated_complement_distance_whole (R : realType) (X : metricType R)
    (d : X->R) :
  is_truncated_complement_distance (@setT X) d -> forall x, d x= 1.
Proof.
move=>hd x; apply/eqP; rewrite eq_le (truncated_complement_distance_cap hd x) /=.
apply: (truncated_complement_distance_greatest hd (lexx _)).
by move=>y hy; exfalso; exact: (hy I).
Qed.
