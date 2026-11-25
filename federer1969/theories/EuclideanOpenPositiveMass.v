(** Federer (1969), 3.2.33, p. 270: a nonempty
    open coordinate piece has positive natural-dimensional
    measure, supporting analytic continuation of rank bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal
  topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanClosedBallGrowth MetricClosedBalls MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_open_positive_mass]: the positive
    measure of nonempty open coordinate pieces in the rank
    argument of Federer 3.2.33, p. 270, using
    the ball volumes of 2.7.16, pp. 134–135.
    A closed ball of half the neighbourhood radius lies
    in the set. Dimension zero is retained. *)
Lemma euclidean_open_positive_mass (R:realType) n
    (U:set (inner_metric_space (@euclidean_inner_productP R n))) a:
  open U ->U a ->(0<euclidean_lebesgue_measure n U)%E.
Proof.
move=>hOpen ha.
have [r hr hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP a U)
  (open_nbhs_nbhs (conj hOpen ha)).
have hHalf:0<r/2 by rewrite divr_gt0 // ltr0n.
have hSmall:r/2<r by lra.
have hSubset:metric_closed_ball a (r/2) `<=` U.
  move=>x hx; apply:hBall; exact:(le_lt_trans hx hSmall).
apply:(lt_le_trans _ (measure_mono (euclidean_lebesgue_is_measure R n) hSubset)).
rewrite (euclidean_closed_ball_measure a hHalf) lte_fin.
apply:mulr_gt0; last exact:exprn_gt0.
exact:(euclidean_closed_unit_volume_laws R n).2.
Qed.
