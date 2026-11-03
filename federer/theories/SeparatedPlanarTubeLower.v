(** Federer (1969), 3.2.40, p. 276: actual
    finite separated planar points give a lower bound for
    the original source's normalized tube at gap/4. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume MetricOpenThickening
  MetricOpenThickeningClosure MinkowskiContents FiniteIndexedSeparatedTube
  FinitePositiveMinkowskiContent MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [separated_indexed_planar_tube_lower_bound]: supporting
    infinite upper content in Federer 3.2.40, p. 276.
    Actual g-separated source points have disjoint balls at
    radius g/4, giving quotient at least N*alpha(2)*g/8.
    No source measurability or tube finiteness is assumed. *)
Lemma separated_indexed_planar_tube_lower_bound (R:realType) (I:finType)
    (W:set (inner_metric_space (@euclidean_inner_productP R 2)))
    (a:I->inner_metric_space (@euclidean_inner_productP R 2)) (g:R):
  (0<g)%R ->(forall i,W (a i)) ->
  (forall i k,i!=k ->(g<=mdist (a i) (a k))%R) ->
  (#|I|%:R*euclidean_unit_ball_volume R 2*g/8)%R%:E<=
    minkowski_tube_quotient 1 W (g/4)%R.
Proof.
move=>hg hInside hSeparated.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose r:=(g/4)%R.
have hr:(0<r)%R by rewrite /r divr_gt0 // ltr0n.
have hTwo:(0<(2:R))%R by rewrite ltr0n.
have hDenominator:(0<2*r)%R:=mulr_gt0 hTwo hr.
have hSeparation i k:i!=k ->(2*r<=mdist (a i) (a k))%R.
  move=>hDifferent; apply:le_trans _ (hSeparated i k hDifferent).
  rewrite /r; lra.
have hSubset:(a @` setT) `<=` W by move=>x [i _ <-]; exact:hInside i.
have hMass:=measure_mono (euclidean_lebesgue_is_measure R 2)
  (@metric_open_thickening_monotone R X (a @` setT) W r hSubset).
rewrite (@finite_indexed_separated_tube_volume R 2 I a r hr hSeparation) in hMass.
have hInverse:0<=((2*r)%R%:E)^-1 by rewrite inve_ge0 lee_fin; exact:ltW hDenominator.
have hScaled:=lee_wpmul2r hInverse hMass.
have hNumerator:(#|I|%:R*(euclidean_unit_ball_volume R 2*r^+2))%R=
    ((#|I|%:R*euclidean_unit_ball_volume R 2)*r^+2)%R by ring.
have hNormalize:=@finite_tube_power_normalization R
  (#|I|%:R*euclidean_unit_ball_volume R 2)%R 2 r 1 1 hTwo hr.
rewrite !expr1 in hNormalize.
rewrite hNumerator hNormalize in hScaled.
have hQuotient:minkowski_tube_quotient 1 W r=
    @euclidean_lebesgue_measure R 2 (metric_open_thickening W r)/(2*r)%R%:E.
  by rewrite /minkowski_tube_quotient euclidean_unit_ball_volume1 expr1.
have hCoefficient:(#|I|%:R*euclidean_unit_ball_volume R 2/2*r)%R=
    (#|I|%:R*euclidean_unit_ball_volume R 2*g/8)%R by rewrite /r; field.
by rewrite -hQuotient hCoefficient in hScaled.
Qed.
