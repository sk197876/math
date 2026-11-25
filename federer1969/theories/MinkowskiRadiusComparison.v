(** Federer (1969), 3.2.40, p. 276: supporting comparisons
    between adjacent positive radii for the two codimension-one
    examples. The actual tube numerator is monotone in radius;
    its normalized quotient need not be monotone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume MinkowskiContents
  MinkowskiContentsBasic MetricOpenThickening MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_open_thickening_radius_monotone]: supporting
    interpolation between tube scales in Federer 3.2.40, p. 276.
    Actual ball membership proves the inclusion for arbitrary
    sources, including empty sources and nonpositive radii. *)
Lemma metric_open_thickening_radius_monotone (R:realType) (X:metricType R)
    (S:set X) (s r:R):
  (s<=r)%R ->metric_open_thickening S s `<=` metric_open_thickening S r.
Proof.
move=>hsr x [a ha hax]; exists a=>//.
exact:lt_le_trans hax hsr.
Qed.

(** Source for [codimension_one_radius_weighted_tube_quotient]: supporting
    cancellation of the positive radius in Federer 3.2.40, p. 276.
    The actual normalizing coefficient is alpha(1)=2. Infinite
    tube volumes are retained; no division by zero is used. *)
Lemma codimension_one_radius_weighted_tube_quotient (R:realType) m
    (S:set (inner_metric_space (@euclidean_inner_productP R m.+1))) (r:R):
  (0<r)%R ->
  r%:E*minkowski_tube_quotient m S r=
    @euclidean_lebesgue_measure R m.+1 (metric_open_thickening S r)/(2:R)%:E.
Proof.
move=>hr.
have hTwo:(0<(2:R))%R by rewrite ltr0n.
have hDenominator:(0<(2*r:R))%R:=mulr_gt0 hTwo hr.
have hScalar:(r*(2*r)^-1)%R=(2^-1)%R.
  by rewrite invfM mulrCA mulfV ?gt_eqF // mulr1.
rewrite /minkowski_tube_quotient subSnn euclidean_unit_ball_volume1 expr1
  !inver (gt_eqF hDenominator) (gt_eqF hTwo) muleCA -EFinM hScalar.
reflexivity.
Qed.

(** Source for [codimension_one_weighted_tube_monotone]: supporting
    actual volume comparison in Federer 3.2.40, p. 276.
    Only the radius-weighted quotient is asserted monotone. *)
Lemma codimension_one_weighted_tube_monotone (R:realType) m
    (S:set (inner_metric_space (@euclidean_inner_productP R m.+1))) (s r:R):
  (0<s)%R ->(s<=r)%R ->
  s%:E*minkowski_tube_quotient m S s<=r%:E*minkowski_tube_quotient m S r.
Proof.
move=>hs hsr; have hr:=lt_le_trans hs hsr.
rewrite (codimension_one_radius_weighted_tube_quotient S hs)
  (codimension_one_radius_weighted_tube_quotient S hr).
apply:lee_wpmul2r.
- rewrite inve_ge0 lee_fin; exact:ler0n.
- apply:(measure_mono (euclidean_lebesgue_is_measure R m.+1)).
  exact:metric_open_thickening_radius_monotone hsr.
Qed.

(** Source for [codimension_one_tube_radius_comparison]: supporting
    all-small-radius interpolation for the compact triangular surface
    cited in Federer 3.2.40, p. 276. If s<=r<=C*s with s>0,
    the quotient at s is at most C times that at r. No
    finiteness of either tube volume is assumed. *)
Lemma codimension_one_tube_radius_comparison (R:realType) m
    (S:set (inner_metric_space (@euclidean_inner_productP R m.+1))) (s r C:R):
  (0<s)%R ->(s<=r)%R ->(r<=C*s)%R ->
  minkowski_tube_quotient m S s<=C%:E*minkowski_tube_quotient m S r.
Proof.
move=>hs hsr hrC.
have hr:=lt_le_trans hs hsr.
have hFinite:s%:E \is a fin_num by rewrite fin_numE.
have hPositive:0<s%:E by rewrite lte_fin.
rewrite -(@lee_pmul2l R s%:E hFinite hPositive).
have hWeighted:=codimension_one_weighted_tube_monotone S hs hsr.
apply:le_trans hWeighted _.
rewrite (@muleA R s%:E C%:E (minkowski_tube_quotient m S r)).
change (is_true (r%:E*minkowski_tube_quotient m S r<=
  (s*C)%R%:E*minkowski_tube_quotient m S r)%E).
apply:lee_wpmul2r; first exact:minkowski_tube_quotient_nonnegative hr.
by rewrite lee_fin (mulrC s C).
Qed.
