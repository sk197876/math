(** Federer (1969), 2.9.16, p. 161: the counterexample using all closed
    balls containing the base point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra num_normedtype.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  InnerNormedTopology InnerNorm EuclideanClosedBallGrowth EuclideanCoordinateMetric
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes EuclideanAdditiveGroup
  MeasureUP MeasureBasic BorelRegularMeasureUP MeasureDerivationContext MetricClosedBalls
  CoveringFamilyUP CoveringRelationUP MetricBoundedUnion NoncenteredBallRelations NoncenteredDoublingVitali.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.


(** Source for [euclidean_lebesgue_derivation_class]: standing
    class M for L^n in Federer 2.9.16, p. 161.
    Borel regularity follows from 2.6.5, and every bounded
    set lies in a compact closed ball, of finite measure.
    The harmless dimension-zero extension is included. *)
Lemma euclidean_lebesgue_derivation_class (R : realType) n :
  is_derivation_measure (@euclidean_lebesgue_measure R n).
Proof.
constructor.
- exact: euclidean_lebesgue_is_measure.
- exact: euclidean_lebesgue_borel_regular.
- move=> A hA.
  have [r [hr hb]] := @metric_bounded_distance_bound R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] A 0%R hA.
  have hm := @measure_mono R _ _ (euclidean_lebesgue_is_measure R n)
    A (metric_closed_ball (0%R : inner_metric_space (@euclidean_inner_productP R n)) r) hb.
  apply: (le_lt_trans hm).
  rewrite euclidean_metric_closed_ballE.
  exact: euclidean_compact_finite (@euclidean_closed_ball_compact R n 0%R r).
Qed.

(** Source for [euclidean_closed_ball_positive]: positive
    denominators for the ball relation in Federer 2.9.16,
    p. 161; the exact ball-volume formula is already
    proved from translation and dilation. Dimension zero has
    unit mass and satisfies the same positive-radius assertion. *)
Lemma euclidean_closed_ball_positive (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n)) (r : R) :
  (0<r)%R -> 0<euclidean_lebesgue_measure n (metric_closed_ball a r).
Proof.
move=> hr; rewrite euclidean_closed_ball_measure // lte_fin mulr_gt0 //.
- exact: (euclidean_closed_unit_volume_laws R n).2.
- by rewrite exprn_gt0.
Qed.

(** Source for [euclidean_noncentered_balls_vitali]: direct
    Vitali assertion for V in Federer 2.9.16, p. 161,
    with the Euclidean norm, in every finite dimension.
    The proof follows the printed references to 2.8.17
    and 2.8.8: diameter enlargement lies in the fivefold
    ball, whose volume is exactly 5^n times the original
    volume. No centered-ball Vitali theorem is substituted. *)
Theorem euclidean_noncentered_balls_vitali (R : realType) n :
  is_vitali_relation (@euclidean_lebesgue_measure R n)
    (@noncentered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]).
Proof.
apply: (@doubling_noncentered_balls_vitali R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
  (@euclidean_lebesgue_measure R n) (5^+n)%R).
- exact: euclidean_lebesgue_derivation_class.
- apply: exprn_ge0; by rewrite ler0n.
- exact: euclidean_closed_ball_positive.
move=> a r hr.
have h5r : (0<5*r)%R by rewrite mulr_gt0 // ltr0n.
rewrite !euclidean_closed_ball_measure // -EFinM exprMn.
have he : (euclidean_closed_unit_volume R n*(5^+n*r^+n)=
    5^+n*(euclidean_closed_unit_volume R n*r^+n))%R by rewrite mulrCA.
by rewrite he.
Qed.
