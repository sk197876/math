(** Federer (1969), 3.2.46, pp. 281–282: a map
    into the original open chart can be regarded as a map
    into its Riemannian metric carrier. Continuity follows
    from the proved equality of the chart topologies; no
    global comparison of either metric is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MetricSubsetBackground RiemannianTensorUP RiemannianMetricCarrier RiemannianMetricTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_chart_lift]: the same original
    map f with its proved image in A, supporting 3.2.46,
    p. 282. This adapter retains every value of f;
    it selects no extension or differential. *)
Definition riemannian_chart_lift (R : realType) (X : Type) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (f : X -> R_n R n) (hf : forall x, A (f x)) (x : X) : riemannian_metric_space hg :=
  @exist [the metricType R of inner_metric_space (@euclidean_inner_productP R n)]
    (fun z=>z \in (A : set (inner_metric_space (@euclidean_inner_productP R n))))
    (f x) (mem_set (hf x)).

(** Source for [riemannian_chart_lift_value]: the adapter
    has exactly the original coordinate value, supporting
    3.2.46, p. 282. *)
Lemma riemannian_chart_lift_value (R : realType) (X : Type) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) f hf x :
  val (@riemannian_chart_lift R X n A g hg f hf x)=f x.
Proof. by []. Qed.

(** Source for [riemannian_chart_lift_continuous]: ordinary
    coordinate continuity gives actual Riemannian continuity,
    supporting the local transformation formulas of 3.2.46,
    p. 282. No global Lipschitz hypothesis is needed. *)
Lemma riemannian_chart_lift_continuous (R : realType) (X : metricType R) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (f : X -> inner_metric_space (@euclidean_inner_productP R n)) hf :
  continuous f -> continuous (@riemannian_chart_lift R X n A g hg f hf).
Proof.
move=> hCont.
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
pose C := [the metricType R of @metric_subset R E A].
pose F := fun x : X=>(@riemannian_chart_lift R X n A g hg f hf x : C).
have hC : continuous F.
  move=> a V hV.
  have [d hd hTarget] := (metricType_numDomainType.nbhs_mdistP (F a) V).1 hV.
  have hNb : nbhs (f a) [set y : E | mdist (f a) y<d].
    apply: (metricType_numDomainType.nbhs_mdistP (f a) _).2.
    by exists d.
  have [e he hSource] := (metricType_numDomainType.nbhs_mdistP a _).1 (hCont a _ hNb).
  apply: (metricType_numDomainType.nbhs_mdistP a _).2.
  exists e=> // x hx; apply: hTarget.
  exact: hSource x hx.
move=> a; exact (continuous_comp (hC a)
  (@riemannian_chart_to_metric_continuous R n A g hg (F a))).
Qed.
