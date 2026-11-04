(** Federer (1969), 3.2.46, pp. 281–282: actual
    Riemannian top-dimensional volume is locally finite and
    has a countable finite-measure open cover. The proved
    continuous positive density and ordinary compact-ball
    volume discharge these properties, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLebesgueCompactInner EuclideanClosedBallCompact
  MetricClosedBalls RadonMeasureUP MeasureBasic MeasureAlmostBasic RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianChartReference RiemannianChartVolumeDensity
  RiemannianVolumeIdentification ContinuousPositiveRelativeControl NonnegativeDensitySetUpperBound
  CountableOpenBaseUP CountableBaseLindelof CountablyMeasurableUP
  MeasureUP MeasureBasic MeasureAlmostBasic TopologicalBorel BorelRegularMeasureUP MeasureBasic MeasureAlmostBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_volume_locally_finite]: each
    original chart point has an actual open neighbourhood
    of finite Riemannian top-volume, supporting 3.2.46,
    p. 282. No bound on the entire chart, global
    metric factor or finite total-volume premise is added. *)
Theorem riemannian_volume_locally_finite (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g) (hp : 0<=m%:R :> R) :
  forall a : riemannian_metric_space hg, exists V : set (riemannian_metric_space hg),
    open V /\ V a /\ (riemannian_hausdorff_measure hg m%:R hp V< +oo)%E.
Proof.
move=> a.
pose X := [the topologicalType of riemannian_metric_space hg].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R m)].
pose phi := @riemannian_chart_reference R m A g hg.
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose j := riemannian_chart_volume_density hg.
have hJ := @riemannian_chart_volume_density_positive R m A g hg a.
have hTwo : (1<2 :> R) by rewrite ltr1n.
have [W [hW [hWa hControl]]] := @continuous_positive_relative_neighbourhood R X j a 2
  (@riemannian_chart_volume_density_continuous R m A g hg) hJ hTwo.
pose Q : set X := (fun x : X=>(val x : E)) @^-1` [set z : E | mdist (val a) z<1].
have hQ : open Q.
  exact (@open_comp X E (fun x=>val x) [set z : E | mdist (val a) z<1]
    (fun x _=>@riemannian_chart_inclusion_continuous R m A g hg x)
    (@metric_open_ball_open R E (val a) 1)).
pose V := W `&` Q.
have hV : open V := openI hW hQ.
have hVa : V a.
  split; first exact hWa; change (is_true (mdist (val a : E) (val a)<1)); by rewrite mdistxx ltr01.
have hImageBound : (fun x : X=>(val x : E)) @` V `<=` metric_closed_ball (val a : E) 1.
  move=> z [x [hxW hxQ] <-]; exact: ltW hxQ.
have hPhiFinite : (phi V< +oo)%E.
  rewrite /phi riemannian_chart_reference_value.
  exact (le_lt_trans (measure_mono (euclidean_lebesgue_is_measure R m) hImageBound)
    (@radon_compact_finite R E (@euclidean_lebesgue_measure R m)
      (@euclidean_lebesgue_radon R m) (metric_closed_ball (val a : E) 1)
      (@euclidean_closed_metric_ball_compact R m (val a) 1))).
have hBound : (mu V<=(2*j a)%:E*phi V)%E.
  apply: (@nonnegative_density_set_upper_bound R X phi mu
    (@riemannian_chart_reference_is_measure R m A g hg)
    (fun x=>(j x)%:E) V (2*j a)
    (@riemannian_chart_reference_regular R m A g hg)
    (@riemannian_volume_density_identification R m A g hg hp)).
  - apply: mulr_gt0; first by rewrite ltr0n.
    exact hJ.
  - move=> x hx; rewrite lee_fin; exact: (hControl x hx.1).2.
exists V; split; first exact hV; split; first exact hVa.
apply: le_lt_trans hBound _.
have hPhiNum : phi V \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative
    (@riemannian_chart_reference_is_measure R m A g hg) V)).
rewrite -(fineK hPhiNum) -EFinM; exact: ltry.
Qed.

(** Source for [riemannian_volume_countably_measurable]:
    a countable finite-volume open cover of the whole
    original chart, supporting 3.2.46, p. 282. Empty
    and disconnected domains and infinite total volume remain. *)
Theorem riemannian_volume_countably_measurable (R : realType) m A g
    (hg : @is_continuous_riemannian_tensor R m A g) (hp : 0<=m%:R :> R) :
  measure_countably_measurable (riemannian_hausdorff_measure hg m%:R hp) setT.
Proof.
pose X := [the topologicalType of riemannian_metric_space hg].
pose mu := riemannian_hausdorff_measure hg m%:R hp.
pose C := [set V : set X | open V /\ (mu V< +oo)%E].
have [U hBase] := @riemannian_chart_countable_open_base R m A g hg.
have hOpen V : C V -> open V by move=> [hV _].
have hCover : setT `<=` \bigcup_(V in C) V.
  move=> x _; have [V [hV [hx hFinite]]] := @riemannian_volume_locally_finite R m A g hg hp x.
  exists V; last exact hx; by split.
have [G [hGC [hCount hGCover]]] := countable_base_open_subcover hBase hOpen hCover.
exists G; split; first exact hCount; split.
- apply/seteqP; split=> x; first exact: hGCover x.
  by move=> _.
- move=> V hV; split; last exact: (hGC V hV).2.
  exact (@borel_regular_borel_measurable R X mu
    (@riemannian_hausdorff_is_measure R m A g hg m%:R hp)
    (@riemannian_hausdorff_borel_regular R m A g hg m%:R hp)
    V (open_borel_set (hGC V hV).1)).
Qed.
