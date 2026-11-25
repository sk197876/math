(** Federer (1969), 3.2.37, p. 274: the Fubini lower bound
    for every actual open tube and every orthogonal projection.
    Arbitrary original source sets and infinite volumes are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNormedTopology
  InnerNorm OrthogonalMaps EuclideanBlockCoordinates EuclideanMetricProduct
  EuclideanLebesgueDimensions EuclideanBallVolume CoordinateProjection OrthogonalProjectionChartUP
  OrthogonalProjectionChart ProjectionChartFubini MetricOpenThickening
  ProductSectionOuterBound ProductSections ProductMeasure MeasurePushforward
  MeasureUP MeasureBasic.
From mathcomp Require Import num_normedtype pseudometric_normed_Zmodule normed_module.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_same_second_block_distance]: supporting
    exact normal-ball fibre in the Fubini argument of Federer
    3.2.37, p. 274. Both coordinate blocks may be zero. *)
Lemma euclidean_same_second_block_distance (R:realType) m k
    (x u:inner_metric_space (@euclidean_inner_productP R m))
    (y:inner_metric_space (@euclidean_inner_productP R k)):
  @mdist R (inner_metric_space (@euclidean_inner_productP R (m+k)))
    (euclidean_block_join (x,y)) (euclidean_block_join (u,y))=mdist x u.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split;
  rewrite -ler_sqr ?nnegrE ?mdist_ge0 //
    (@euclidean_block_squared_distance R m k) !euclidean_block_joinK /=
    mdistxx !expr2 ?mul0r ?addr0; exact:lexx.
Qed.

(** Source for [projection_chart_tube_normal_ball]: every nonempty
    projected source fibre contains a whole normal open r-ball
    in the tube, Federer 3.2.37, p. 274. The original source
    is arbitrary, with no Borel or boundedness hypothesis. *)
Lemma projection_chart_tube_normal_ball (R:realType) m k
    (p:{linear R_n R (m+k)->R_n R k})
    (f g:{linear R_n R (m+k)->R_n R (m+k)})
    (hc:is_orthogonal_projection_chart p f g)
    (S:set (inner_metric_space (@euclidean_inner_productP R (m+k))))
    (a:inner_metric_space (@euclidean_inner_productP R (m+k))) (r:R): S a ->
  [set x:inner_metric_space (@euclidean_inner_productP R m)|
    (mdist (euclidean_block_split (f a)).1 x<r)%R] `<=`
  product_horizontal_section
    ((fun z=>g (@euclidean_block_join R m k z)) @^-1` metric_open_thickening S r) (p a).
Proof.
move=>ha x hx.
have hMetric (u v:inner_metric_space (@euclidean_inner_productP R (m+k))):
  @mdist R (inner_metric_space (@euclidean_inner_productP R (m+k))) (f u) (f v)=mdist u v.
  rewrite !inner_metric_distanceE -linearB.
  exact:(@orthogonal_map_norm R (R_n R (m+k)) (R_n R (m+k))
    (@euclidean_inner_product R (m+k)) (@euclidean_inner_product R (m+k))
    (@euclidean_inner_productP R (m+k)) (@euclidean_inner_productP R (m+k))
    f (projection_chart_orthogonal_law hc) (u-v)).
exists a=>//.
change (is_true (mdist a (g (euclidean_block_join (x,p a)))<r)%R).
rewrite -(hMetric a _) (projection_chart_backward_inverse_law hc).
have hfa:f a=euclidean_block_join ((euclidean_block_split (f a)).1,p a).
  rewrite -(projection_chart_coordinate_law hc a).
  exact:esym (euclidean_block_splitK (f a)).
by rewrite hfa euclidean_same_second_block_distance.
Qed.

(** Source for [euclidean_projection_tube_lower_bound]: the actual
    normalized-tube estimate before taking liminf in Federer
    3.2.37, p. 274. The outer-section Fubini lower bound of
    2.6.2 applies to every source subset, including nonmeasurable
    projections and infinite masses. Positive normalization also
    holds when the normal block or projection block is zero. *)
Theorem euclidean_projection_tube_lower_bound (R:realType) m k
    (p:{linear R_n R (m+k)->R_n R k})
    (S:set (inner_metric_space (@euclidean_inner_productP R (m+k)))) (r:R):
  O_star p -> (0<r)%R ->
  (euclidean_unit_ball_volume R m*r^+m)%:E*
    @euclidean_lebesgue_measure R k (p @` S)<=
    @euclidean_lebesgue_measure R (m+k) (metric_open_thickening S r).
Proof.
move=>hp hr.
pose f:=(@orthogonal_projection_chart R m k p hp).1.
pose g:=(@orthogonal_projection_chart R m k p hp).2.
have hc:=@orthogonal_projection_chart_specification R m k p hp.
pose X:=inner_metric_space (@euclidean_inner_productP R (m+k)).
pose T:=metric_open_thickening S r.
pose H:=fun z=>g (@euclidean_block_join R m k z).
pose F:=fun z:X=>@euclidean_block_split R m k (f z).
pose K:=H @^-1` T.
have hpre:F @^-1` K=T.
  apply/seteqP; split=>z;
    change (T (g (euclidean_block_join (euclidean_block_split (f z))))->T z) ||
    change (T z->T (g (euclidean_block_join (euclidean_block_split (f z)))));
    by rewrite euclidean_block_splitK (projection_chart_forward_inverse_law hc).
have hMass:product_measure (euclidean_lebesgue_is_measure R m)
    (euclidean_lebesgue_is_measure R k) K=@euclidean_lebesgue_measure R (m+k) T.
  rewrite -(projection_chart_product_measure hc).
  by rewrite /measure_pushforward hpre.
rewrite -hMass.
apply:product_horizontal_sections_outer_lower_bound.
- apply:mulr_gt0; first exact:(euclidean_unit_ball_volumeE R m).2.
  exact:exprn_gt0 _ hr.
- move=>y [a ha <-].
  have hb:=@projection_chart_tube_normal_ball R m k p f g hc S a r ha.
  have hB:@euclidean_lebesgue_measure R m
      [set x:inner_metric_space (@euclidean_inner_productP R m)|
        (mdist (euclidean_block_split (f a)).1 x<r)%R]=
      (euclidean_unit_ball_volume R m*r^+m)%:E.
    have hE:[set x:inner_metric_space (@euclidean_inner_productP R m)|
        (mdist (euclidean_block_split (f a)).1 x<r)%R]=
        [set x:inner_metric_space (@euclidean_inner_productP R m)|
          (`|x-(euclidean_block_split (f a)).1|<r)%R].
      apply/seteqP; split=>x.
      + change ((mdist (euclidean_block_split (f a)).1 x<r)%R ->
          (`|x-(euclidean_block_split (f a)).1|<r)%R).
        by rewrite inner_metric_normE.
      + change ((`|x-(euclidean_block_split (f a)).1|<r)%R ->
          (mdist (euclidean_block_split (f a)).1 x<r)%R).
        by rewrite inner_metric_normE.
    rewrite hE; exact:(@euclidean_ball_measure R m (euclidean_block_split (f a)).1 r hr).
  rewrite -hB; exact:(@measure_mono R (inner_metric_space (@euclidean_inner_productP R m))
    (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) _ _ hb).
Qed.
