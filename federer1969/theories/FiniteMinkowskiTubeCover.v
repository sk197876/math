(** Federer (1969), 3.2.38, p. 275: the normalized tube
    of the original image is bounded by the finite sum of cell tubes. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume MetricOpenThickening MinkowskiContents MinkowskiContentsBasic
  MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_minkowski_image_tube_cover]: the first
    inequality in the final display of Federer 3.2.38, p. 275.
    Actual image points and tube centres give the finite cover;
    measure subadditivity and a proved positive normalizer give the
    sum of actual normalized tube volumes. Source and covering
    pieces need not be measurable, and the finite family may be empty. *)
Lemma finite_minkowski_image_tube_cover (R:realType) (X:Type) n m (I:finType)
    (f:X->inner_metric_space (@euclidean_inner_productP R n))
    (C:set X) (Q:I->set X) (r:R):
  (0<r)%R ->C `<=` \bigcup_i Q i ->
  minkowski_tube_quotient m (f @` C) r<=\sum_i minkowski_tube_quotient m (f @` Q i) r.
Proof.
move=>hr hCover.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
have hTubes:metric_open_thickening (f @` C) r `<=`
    \bigcup_i metric_open_thickening (f @` Q i) r.
  move=>z [y [x hx <-] hDistance]; have [i _ hi]:=hCover x hx.
  exists i; first exact Logic.I.
  exists (f x).
  - exists x; [exact hi|reflexivity].
  - exact hDistance.
have hMeasure:=@measure_finite_indexed_cover R Y I mu hm _ _ hTubes.
have hDenominator:=minkowski_tube_denominator_positive n m hr.
have hInverse:0<=((euclidean_unit_ball_volume R (n-m)*r^+(n-m))%R%:E)^-1.
  rewrite inver (gt_eqF hDenominator) lee_fin invr_ge0; exact:ltW hDenominator.
have hScaled:=lee_wpmul2r hInverse hMeasure.
rewrite /minkowski_tube_quotient.
apply:le_trans hScaled _.
rewrite ge0_sume_distrl; first exact:lexx.
move=>i _; exact:measure_nonnegative hm _.
Qed.
