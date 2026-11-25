(** Federer (1969), 3.2.46, pp. 281–282: the
    proved chart topology permits localization on actual
    ambient Euclidean open sets. These supporting adapters
    retain exactly the original chart points, with no
    replacement coordinate domain or selected frame field. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology subtype_topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MetricSubsetBackground RiemannianTensorUP RiemannianMetricCarrier
  RiemannianMetricTopology RiemannianReferencePushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [riemannian_chart_open_coordinate_image]:
    an open set of the actual Riemannian chart has an
    open original coordinate image in R^n, supporting
    3.2.46, p. 282. Use the proved identity of
    topologies and the original openness of A. *)
Lemma riemannian_chart_open_coordinate_image (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (V : set (riemannian_metric_space hg)) :
  open V -> @open [the topologicalType of inner_metric_space (@euclidean_inner_productP R n)]
    ((fun x : riemannian_metric_space hg=>val x) @` V).
Proof.
move=> hV.
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose C := [the metricType R of @metric_subset R E A].
pose M := [the metricType R of riemannian_metric_space hg].
have hChart := @open_comp C M (@riemannian_chart_to_metric R n A g hg) V
  (fun x _=>@riemannian_chart_to_metric_continuous R n A g hg x) hV.
change (@open C V) in hChart.
have [O hO hEq] := hChart.
have hImage : (fun x : M=>(val x : E)) @` V=A `&` O.
  apply/seteqP; split=> y.
  - move=> [x hx <-]; split; first exact: set_valP x.
    by rewrite -hEq in hx.
  - move=> [hyA hyO].
    pose x : M := @exist E (fun z=>z \in (A : set E)) y (mem_set hyA).
    exists x; last by [].
    by rewrite -hEq.
rewrite hImage; apply: openI; first exact (@riemannian_chart_domain_open R n A g hg).
exact hO.
Qed.

(** Source for [riemannian_chart_coordinate_patch]: every
    original open chart patch corresponds to an actual
    ambient open subset W of A, with exact membership
    under the original inclusion. Supporting localization
    of 3.2.46, p. 282; the point set is retained. *)
Lemma riemannian_chart_coordinate_patch (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (V : set (riemannian_metric_space hg)) :
  open V -> exists W : set (inner_metric_space (@euclidean_inner_productP R n)),
    open W /\ W `<=` A /\ forall x : riemannian_metric_space hg, W (val x) <-> V x.
Proof.
move=> hV.
exists ((fun x : riemannian_metric_space hg=>val x) @` V); split.
- exact: riemannian_chart_open_coordinate_image hV.
- split.
  + move=> y [x hx <-]; exact: set_valP x.
  + move=> x; split.
    * move=> [y hy hEq]; have hxy : y=x := val_inj hEq; by rewrite -hxy.
    * move=> hx; by exists x.
Qed.
