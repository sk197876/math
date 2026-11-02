(** Federer (1969), 3.1.24, p. 240: applying
    2.9.11 to the measurable zero set and removing a null
    subset gives a set of density one at every own point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanClosedBallVolume EuclideanNoncenteredVitali EuclideanApproximateContext EuclideanZeroDensityUnion
  CenteredBallRelations MetricClosedBalls PartialFunctionUP MeasureUP MeasureBasic MeasureAlmostBasic
  MeasureSetDensity MeasureDensityPoints DensityMeasurableSets CenteredNullSetDensity LocalZeroDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_full_density_core_exists]: supporting
    the set Z in Federer 3.1.24, p. 240. A measurable
    set E contains a subset S with E minus S null, whose
    complement has density zero at every point of S. This
    expands the null-set removal implicit in the printed
    approximate-differentiation argument. *)
Theorem euclidean_full_density_core_exists (R:realType) n
    (E:set (inner_metric_space (@euclidean_inner_productP R n))) :
  measure_measurable (@euclidean_lebesgue_measure R n) E ->
  exists S:set (inner_metric_space (@euclidean_inner_productP R n)),
    (forall x,S x -> E x) /\ euclidean_lebesgue_measure n (E `\` S)=0%E /\
    forall x,S x -> partial_function_graph
      (measure_set_density (@euclidean_lebesgue_measure R n)
        (@centered_closed_ball_relation R
          [the metricType R of inner_metric_space (@euclidean_inner_productP R n)])
        (~` S)) x 0%E.
Proof.
move=>hE.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose V:=@centered_closed_ball_relation R [the metricType R of X].
have hm:=euclidean_lebesgue_is_measure R n.
pose Q:=measure_density_complement_zero_points mu V E.
pose S:=E `&` Q.
have hNull:mu (E `\` Q)=0%E.
  exact ((density_complement_zero_points_conclusions E (euclidean_approximate_context R n)).2.2.2.1 hE).
have hNS:mu (E `\` S)=0%E.
  apply: (measure_null_subset hm _ hNull)=>x [hx hn].
  split; first exact hx; by move=>hQ; apply:hn; split.
exists S; split; first by move=>x hx; exact hx.1.
split; first exact hNS.
move=>x hx.
have hballs (y:X) (r:R) (hr:0<r):
    (0<mu (metric_closed_ball y r))%E /\ mu (metric_closed_ball y r) \is a fin_num.
  split; first exact (@euclidean_closed_ball_positive R n y r hr).
  by rewrite /mu (euclidean_closed_ball_normalized_volume y (ltW hr)) fin_numE.
have hbad:=@centered_null_set_density_zero R [the metricType R of X] mu (E `\` S) x hm hballs hNS.
have hUnion:=euclidean_zero_density_union hx.2 hbad.
apply: (@local_zero_density_mono R [the metricType R of X] mu V
  (~` S) ((~` E) `|` (E `\` S)) setT x (euclidean_approximate_context R n) openT Logic.I _ hUnion).
move=>y _ hn; case:(pselect (E y))=>[hy|hy]; last by left.
right; by split.
Qed.
