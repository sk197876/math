(** Federer (1969), 3.3.4, p. 291: transport
    the actual restricted reference balls to the
    Euclidean coordinates in which 3.2.19, p. 256,
    applies. All chart witnesses remain local and
    every original source subset is retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric FiniteInnerChartUP FiniteInnerChartCompact
  MetricSubsetBackground HausdorffMeasure HausdorffMetricSubset
  MetricClosedBalls MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_inverse_chart_metric]:
    supporting actual metric identity in the local
    Euclidean coordinates for Federer 3.3.4, p. 291.
    It follows from the independently specified
    chart inverse and inner-product laws. *)
Lemma finite_inner_inverse_chart_metric (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)):
  is_finite_inner_chart B e p ->
  forall x y:inner_metric_space hB,
  mdist (p x:inner_metric_space (@euclidean_inner_productP R n)) (p y)=mdist x y.
Proof.
move=>hChart x y; rewrite !inner_metric_distanceE -linearB.
exact:(@finite_inner_chart_inverse_norm R V B hB n e p hChart (x-y)).
Qed.

(** Source for [finite_inner_subset_closed_ball_image]:
    the original restricted closed balls in the
    3.2.19 application of Federer 3.3.4, p. 291,
    agree exactly with closed balls in the
    local Euclidean chart. No hull is used. *)
Lemma finite_inner_subset_closed_ball_image (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (S:set (inner_metric_space hB)) (a:inner_metric_space hB) (r:R):
  is_finite_inner_chart B e p ->
  p @` (S `&` metric_closed_ball a r)=
    (p @` S) `&` metric_closed_ball (p a:inner_metric_space (@euclidean_inner_productP R n)) r.
Proof.
move=>hChart; apply/seteqP; split=>z.
- move=>[x [hx hNear] <-]; split; first by exists x.
  change (is_true (mdist (p a:inner_metric_space (@euclidean_inner_productP R n)) (p x)<=r)).
  by rewrite (@finite_inner_inverse_chart_metric R V B hB n e p hChart a x).
- move=>[[x hx <-] hNear]; exists x=>//; split=>//.
  change (is_true (mdist a x<=r)).
  change (is_true (mdist (p a:inner_metric_space (@euclidean_inner_productP R n)) (p x)<=r)) in hNear.
  by rewrite (@finite_inner_inverse_chart_metric R V B hB n e p hChart a x) in hNear.
Qed.

(** Source for [finite_inner_subset_ball_mass_transport]:
    actual restricted Hausdorff ball masses agree
    in the inherited metric and Euclidean chart,
    supporting Federer 3.3.4, p. 291. This
    includes all real radii, all natural degrees
    and arbitrary original subsets S. *)
Theorem finite_inner_subset_ball_mass_transport (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (S:set (inner_metric_space hB)) q
    (a:metric_subset S) (r:R):
  is_finite_inner_chart B e p ->
  @hausdorff_measure R [the metricType R of metric_subset S] q (metric_closed_ball a r)=
    measure_restrict (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) q)
      (p @` S) (metric_closed_ball (p (val a):inner_metric_space (@euclidean_inner_productP R n)) r).
Proof.
move=>hChart.
have hSub:=@hausdorff_metric_subset_preimage R (inner_metric_space hB) S
  (metric_closed_ball (val a) r) q.
have hBall:(fun x:metric_subset S=>(val x:inner_metric_space hB)) @^-1`
    metric_closed_ball (val a) r=metric_closed_ball a r.
  by apply/seteqP; split=>x.
rewrite hBall in hSub; rewrite hSub /measure_restrict.
rewrite -(@finite_inner_subset_closed_ball_image R V B hB n e p S (val a) r hChart).
symmetry; exact:(@finite_inner_chart_inverse_hausdorff R V B hB n e p hChart q _).
Qed.
