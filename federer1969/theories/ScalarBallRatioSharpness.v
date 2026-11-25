(** Federer (1969), 2.9.18(1), p. 163: sharpness of the upper-limit
    conclusion. The printed book uses nonempty intersection in the
    weighted-hit formula. The May 1987 erratum, p. 3, book p. 163 line 11,
    instead prints empty intersection; the original scan confirms that
    reading. ErratumWeightedHitCounterexample.v shows that this replacement
    would give the empty set positive value, so the book's
    nonempty-intersection condition is retained. This is a correction to the
    erratum, not a transcription change. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MetricClosedBalls PartialFunctionUP MeasureDerivates
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureDerivationContext BorelRegularMeasureUP
  TopologicalBorel PositiveRightOrderLimit LebesgueScalarMeasure ScalarLebesgueBallContext
  NoncenteredBallRelations NowhereDenseUP PositiveNowhereDenseCompact WeightedHitMeasure
  SparseBallCoverSequenceUP SparseBallCoverSequence SparseWeightedHitBounds SparseBallRatioOscillation
  CenteredBallRatioDomain RadialBallRatios RadialBallLowerLimit UpperBallRatioDichotomy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section ScalarSharpness.
Variable R : realType.
Local Notation M := (real_line_metric R).
Local Notation phi := (@lebesgue_scalar_measure R).

(** Source for [sparse_scalar_lower_ratio_zero]: direct zero
    lower radial ratio in Federer 2.9.18(1), p. 163.
    The cofinal small endpoint ratios and nonnegative actual
    graph values give the literal lower positive-radius limit. *)
Lemma sparse_scalar_lower_ratio_zero (T : set M) (c : nat -> R) (S : nat -> set M) (x : M) :
  is_sparse_ball_cover_sequence T c S -> T x ->
  centered_ball_ratio_lower_limit (weighted_hit_measure c S) phi x=0.
Proof.
move=> h hx.
apply: (@centered_ball_ratio_lower_limit_zero R [the metricType R of M]
  (weighted_hit_measure c S) phi x (weighted_hit_measure_is_measure c S) (lebesgue_scalar_is_measure R)).
move=> d e hd he.
have [r [/andP [hr hrd] hsmall]] := sparse_low_ratio_arbitrarily_small h hx hd he.
have hq := @centered_ball_ratio_positive_domain R [the metricType R of M] phi
  (weighted_hit_measure c S) x r (scalar_lebesgue_derivation_class R)
  (@scalar_lebesgue_no_null_ball_points R x) hr.
exists r,(weighted_hit_measure c S (metric_closed_ball x r)/phi (metric_closed_ball x r)).
split; first by apply/andP; split.
by split.
Qed.

(** Source for [sparse_scalar_upper_ratio_ge_half]: direct
    pointwise lower bound 1/2 on the upper radial ratio
    in Federer 2.9.18(1), p. 163. Every
    positive-radius cutoff contains an actual quotient equal
    to 1/2, and every denominator is positive finite. *)
Lemma sparse_scalar_upper_ratio_ge_half (T : set M) (c : nat -> R) (S : nat -> set M) (x : M) :
  is_sparse_ball_cover_sequence T c S -> T x ->
  ((1/2)%R : R)%:E<=centered_ball_ratio_upper_limit (weighted_hit_measure c S) phi x.
Proof.
move=> h hx; apply: centered_ball_ratio_upper_bound_from_cofinal_value=> d hd.
have [r [/andP [hr hrd] hhalf]] := sparse_high_ratio_arbitrarily_small h hx hd.
have hq := @centered_ball_ratio_positive_domain R [the metricType R of M] phi
  (weighted_hit_measure c S) x r (scalar_lebesgue_derivation_class R)
  (@scalar_lebesgue_no_null_ball_points R x) hr.
exists r; split; first by apply/andP; split.
by rewrite hhalf in hq.
Qed.

(** Source for [sparse_scalar_upper_ratio_infinite_ae]: direct
    final use of 2.9.17 in Federer 2.9.18(1),
    p. 163. On a measurable target the
    numerator-null property and uniform Lebesgue growth give
    the zero-or-infinite alternative; the pointwise 1/2
    bound excludes zero. The numerator is the book's
    outer measure and need not be Borel regular. *)
Lemma sparse_scalar_upper_ratio_infinite_ae (T : set M) (c : nat -> R) (S : nat -> set M) :
  is_sparse_ball_cover_sequence T c S -> measure_measurable phi T ->
  measure_almost_everywhere_on phi T
    [set x | centered_ball_ratio_upper_limit (weighted_hit_measure c S) phi x= +oo].
Proof.
move=> h hT.
pose psi := weighted_hit_measure c S.
have hctx : @is_measure_derivation_context R [the metricType R of M] phi
    (@noncentered_closed_ball_relation R [the metricType R of M]).
  constructor; [exact: scalar_lebesgue_derivation_class|exact: scalar_lebesgue_noncentered_balls_vitali].
have hgen := @federer_2_9_17 R [the metricType R of M] phi psi
  (@noncentered_closed_ball_relation R [the metricType R of M]) T 6%R 1%R
  hctx (weighted_hit_measure_is_measure c S) (ltr01)
  (@scalar_lebesgue_uniform_fivefold_growth R 1%R) hT (sparse_weighted_hit_target_null h).
apply: (@measure_null_subset R M phi (lebesgue_scalar_is_measure R) _ _ _ hgen).
move=> x [hx hn]; split=> // -[hz|hinf]; last exact: hn hinf.
have hb := sparse_scalar_upper_ratio_ge_half h hx.
rewrite hz in hb.
have hp : 0<((1/2)%R : R)%:E by rewrite lte_fin divr_gt0 // ltr0n.
by have := lt_le_trans hp hb; rewrite ltxx.
Qed.

(** Source for [federer_2_9_18_1]: complete first sharpness
    example in Federer 2.9.18(1), p. 163,
    for every compact nowhere dense target of positive
    length. The chosen sequences satisfy all printed laws,
    their weighted-hit formula is a measure null on T,
    the lower ratio is zero and upper ratio at least
    1/2 at every target point, the upper ratio is
    infinite almost everywhere on T, and no ordinary
    extended-real radius limit exists at any target point.
    The book's nonempty-intersection convention is retained;
    the erratum's contrary condition is refuted separately. *)
Theorem federer_2_9_18_1 (T : set M) :
  compact T -> is_nowhere_dense T -> 0<phi T ->
  exists (c : nat -> R) (S : nat -> set M),
    is_sparse_ball_cover_sequence T c S /\ is_measure (weighted_hit_measure c S) /\
    weighted_hit_measure c S T=0 /\
    (forall x, T x ->
      centered_ball_ratio_lower_limit (weighted_hit_measure c S) phi x=0 /\
      ((1/2)%R : R)%:E<=centered_ball_ratio_upper_limit (weighted_hit_measure c S) phi x /\
      ~ exists l : \bar R, positive_right_extended_order_limit
        (fun r => weighted_hit_measure c S (metric_closed_ball x r)/phi (metric_closed_ball x r)) l) /\
    measure_almost_everywhere_on phi T
      [set x | centered_ball_ratio_upper_limit (weighted_hit_measure c S) phi x= +oo].
Proof.
move=> hT hnd hp.
have hTn : T !=set0.
  apply: contrapT=> hn.
  have he : T=set0.
    apply/seteqP; split=> x; last by move=> [].
    move=> hx; exfalso; apply: hn; by exists x.
  by rewrite he (measure_empty (lebesgue_scalar_is_measure R)) ltxx in hp.
pose c := @sparse_ball_cover_radii R [the metricType R of M] T hT hnd hTn.
pose S := @sparse_ball_cover_centers R [the metricType R of M] T hT hnd hTn.
have h := @sparse_ball_cover_sequence_laws R [the metricType R of M] T hT hnd hTn.
have hTmeas : measure_measurable phi T.
  apply: (@borel_regular_borel_measurable R M phi (lebesgue_scalar_is_measure R)
    (lebesgue_scalar_borel_regular R) T).
  exact: closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of M]) hT).
exists c,S; split=> //; split; first exact: weighted_hit_measure_is_measure.
split; first exact: sparse_weighted_hit_target_null h.
split.
- move=> x hx; split; first exact: sparse_scalar_lower_ratio_zero h hx.
  split; [exact: sparse_scalar_upper_ratio_ge_half h hx|exact: sparse_ball_ratio_no_ordinary_limit h hx].
- exact: sparse_scalar_upper_ratio_infinite_ae h hTmeas.
Qed.

(** Source for [federer_2_9_18_1_target_exists]: existence of
    a nonvacuous target for the first example in Federer
    2.9.18(1), p. 163. The target is
    constructed from a small dense open set, so the
    positive-length hypothesis of the preceding complete
    sharpness theorem is actually satisfiable. *)
Theorem federer_2_9_18_1_target_exists :
  exists T : set M, compact T /\ is_nowhere_dense T /\ 0<phi T.
Proof. exact: positive_length_nowhere_dense_compact_exists. Qed.
End ScalarSharpness.
