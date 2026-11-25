(** Federer (1969), 3.2.40, p. 276: supporting ball-volume
    bounds for the actual tubes of finite Cantor-square covers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNormedTopology
  EuclideanLebesgueDimensions EuclideanBallVolume MetricOpenThickening
  MetricDiameter MetricDiameterUP MeasureUP MeasureBasic FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory
  numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_tube_diameter_volume_bound]: supporting
    the level-square tube estimate in Federer 3.2.40, p. 276,
    using the actual Euclidean ball mass of 2.7.16, p. 139.
    No source measurability is assumed. The empty source is
    treated by its empty actual tube, without a chosen centre. *)
Lemma euclidean_tube_diameter_volume_bound (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (d r:R):
  (0<=d)%R ->(0<r)%R ->extended_metric_diameter S<=d%:E ->
  @euclidean_lebesgue_measure R n (metric_open_thickening S r)<=
    (euclidean_unit_ball_volume R n*(d+r)^+n)%R%:E.
Proof.
move=>hd hr hDiameter.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
case:(pselect (exists a,S a))=>[[a ha]|hEmpty].
- have hRadius:(0<d+r)%R by lra.
  have hSubset:metric_open_thickening S r `<=` [set z:X|(`|z-a|<d+r)%R].
    move=>z [y hy hyz].
    have hDistance:(mdist a y<=d)%R.
      have h:=le_trans (metric_diameter_upper (extended_metric_diameter_specification S) ha hy) hDiameter.
      by move:h; rewrite lee_fin.
    have hTriangle:=metric_triangle a y z.
    change (is_true (mdist y z<r)%R) in hyz.
    change (is_true (`|z-a|<d+r)%R).
    rewrite -inner_metric_normE; lra.
  have h:=measure_mono hm hSubset.
  by rewrite (@euclidean_ball_measure R n a (d+r)%R hRadius) in h.
- have hS:S=set0.
    apply/seteqP; split=>[x hx|x hx]; last by [].
    exfalso; apply:hEmpty; by exists x.
  rewrite hS /metric_open_thickening.
  have hTube:(\bigcup_(a in @set0 X) [set x:X|(mdist a x<r)%R])=set0.
    apply/seteqP; split=>[x [a ha _]|x hx]; by [].
  rewrite hTube (measure_empty hm) lee_fin.
  apply:mulr_ge0.
  - exact:ltW (euclidean_unit_ball_volumeE R n).2.
  - have hNonnegative:(0<=d+r)%R by lra.
    exact:(exprn_ge0 n hNonnegative).
Qed.

(** Source for [euclidean_finite_diameter_tube_cover_bound]: supporting
    finite level cover in Federer 3.2.40, p. 276. Count covering
    indices even when their images agree. Arbitrary original W
    and covering pieces are allowed, including an empty family. *)
Lemma euclidean_finite_diameter_tube_cover_bound (R:realType) n (I:finType)
    (W:set (inner_metric_space (@euclidean_inner_productP R n)))
    (S:I->set (inner_metric_space (@euclidean_inner_productP R n))) (d r:R):
  (0<=d)%R ->(0<r)%R ->W `<=` \bigcup_i S i ->
  (forall i,extended_metric_diameter (S i)<=d%:E) ->
  @euclidean_lebesgue_measure R n (metric_open_thickening W r)<=
    (#|I|%:R*(euclidean_unit_ball_volume R n*(d+r)^+n))%R%:E.
Proof.
move=>hd hr hCover hDiameter.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
have hTubes:metric_open_thickening W r `<=` \bigcup_i metric_open_thickening (S i) r.
  move=>z [y hy hyz]; have [i _ hi]:=hCover y hy.
  exists i; first exact Logic.I.
  by exists y.
apply:le_trans (@measure_finite_indexed_cover R X I mu hm _ _ hTubes) _.
have hSum:((\sum_i mu (metric_open_thickening (S i) r))<=
    (\sum_(i:I) (euclidean_unit_ball_volume R n*(d+r)^+n)%R%:E))%E.
  apply:lee_sum=>i _; exact:euclidean_tube_diameter_volume_bound hd hr (hDiameter i).
apply:le_trans hSum _.
rewrite sumEFin sumr_const cardT.
by rewrite (mulr_natl (euclidean_unit_ball_volume R n*(d+r)^+n)%R (size (enum I))).
Qed.
