(** Federer (1969), 3.2.40, p. 276: supporting
    normalization of finite small-square tube covers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanTubeDiameterBound
  MetricOpenThickening MetricDiameter MinkowskiContents
  FinitePositiveMinkowskiContent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_planar_scaled_tube_cover_bound]: supporting
    level-square quotient estimate in Federer 3.2.40, p. 276.
    Covering pieces of diameter at most d*s give an actual
    tube bound at radius s>0. The source and pieces need not
    be measurable. The finite index family may be empty. *)
Lemma finite_planar_scaled_tube_cover_bound (R:realType) (I:finType)
    (W:set (inner_metric_space (@euclidean_inner_productP R 2)))
    (Q:I->set (inner_metric_space (@euclidean_inner_productP R 2))) (d s:R):
  (0<=d)%R ->(0<s)%R ->W `<=` \bigcup_i Q i ->
  (forall i,extended_metric_diameter (Q i)<=(d*s)%R%:E) ->
  minkowski_tube_quotient 1 W s<=
    (#|I|%:R*euclidean_unit_ball_volume R 2*(d+1)^+2/2*s)%R%:E.
Proof.
move=>hd hs hCover hDiameter.
have hD:(0<=d*s)%R:=mulr_ge0 hd (ltW hs).
have hVolume:=@euclidean_finite_diameter_tube_cover_bound R 2 I W Q (d*s)%R s hD hs hCover hDiameter.
have hTwo:(0<(2:R))%R by rewrite ltr0n.
have hDenominator:(0<2*s)%R:=mulr_gt0 hTwo hs.
have hInverse:0<=((2*s)%R%:E)^-1 by rewrite inve_ge0 lee_fin; exact:ltW hDenominator.
have hBound:=lee_wpmul2r hInverse hVolume.
have hAlgebra:(#|I|%:R*(euclidean_unit_ball_volume R 2*(d*s+s)^+2))%R=
    ((#|I|%:R*euclidean_unit_ball_volume R 2*(d+1)^+2)*s^+2)%R by ring.
have hNormalize:=@finite_tube_power_normalization R
  (#|I|%:R*euclidean_unit_ball_volume R 2*(d+1)^+2)%R 2 s 1 1 hTwo hs.
rewrite !expr1 in hNormalize.
rewrite hAlgebra hNormalize in hBound.
have hQuotient:minkowski_tube_quotient 1 W s=
    @euclidean_lebesgue_measure R 2 (metric_open_thickening W s)/(2*s)%R%:E.
  by rewrite /minkowski_tube_quotient euclidean_unit_ball_volume1 expr1.
by rewrite hQuotient.
Qed.
