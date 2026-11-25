(** Federer (1969), 3.2.46, pp. 281–282: the
    ordinary Euclidean reference measure on the original
    chart points. Its topology, Borel sets and countable
    base are connected to the proved rho topology explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric MetricSubsetBackground MetricSubsetSeparability EuclideanMetricSeparability
  SeparableMetricBaseSealed CountableOpenBaseUP HomeomorphicCountableBase
  HausdorffMeasure HausdorffClosedCoverAgreement HausdorffMetricSubset EuclideanHausdorffLebesgue EuclideanLebesgueDimensions
  MeasureUP RegularMeasureUP BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages
  RiemannianTensorUP RiemannianMetricCarrier RiemannianMetricTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Reference.
Context (R : realType) n A g (hg : @is_continuous_riemannian_tensor R n A g).
Local Notation E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
Local Notation C := [the metricType R of @metric_subset R E A].
Local Notation M := [the metricType R of riemannian_metric_space hg].

(** Source for [riemannian_chart_reference]: ordinary
    top-degree Euclidean Hausdorff measure restricted to
    the actual chart points, supporting 3.2.46, p. 281.
    It will be proved equal to L^n of the inclusion image. *)
Definition riemannian_chart_reference : set M -> \bar R :=
  @hausdorff_measure R C n.

(** Source for [riemannian_chart_reference_value]: the
    actual reference mass is L^n of the original point set,
    supporting 3.2.46, pp. 281–282, including dimension zero. *)
Lemma riemannian_chart_reference_value (S : set M) :
  riemannian_chart_reference S = euclidean_lebesgue_measure n
    ((fun x : M=>(val x : E)) @` S).
Proof.
rewrite /riemannian_chart_reference -(@hausdorff_metric_subset_measure R E A n S).
exact: (euclidean_hausdorff_spherical_lebesgue _).1.
Qed.

(** Source for [riemannian_chart_reference_is_measure]:
    the original reference outer measure obeys the earlier
    Hausdorff laws, supporting 3.2.46, pp. 281–282. *)
Lemma riemannian_chart_reference_is_measure : is_measure riemannian_chart_reference.
Proof. exact (@hausdorff_measure_is_measure R C n). Qed.

(** Source for [riemannian_chart_reference_regular]: its
    equal-mass measurable hull law follows from the actual
    Euclidean Hausdorff Borel regularity, supporting 3.2.46,
    pp. 281–282. No null excess is assumed for arbitrary sets. *)
Lemma riemannian_chart_reference_regular : is_regular_measure riemannian_chart_reference.
Proof.
exact (@borel_regular_is_regular R C (@hausdorff_measure R C n)
  (@hausdorff_measure_is_measure R C n) (@hausdorff_measure_borel_regular R C n)).
Qed.

(** Source for [riemannian_chart_reference_borel_measurable]:
    rho Borel sets are ordinary chart Borel sets through the
    proved continuous identity, supporting 3.2.46, pp. 281–282.
    No equivalence of completed sigma algebras is assumed. *)
Lemma riemannian_chart_reference_borel_measurable (B : set M) :
  borel_set B -> measure_measurable riemannian_chart_reference B.
Proof.
move=> hB.
have hPre := @continuous_borel_preimage C M
  (@riemannian_chart_to_metric R n A g hg)
  (@riemannian_chart_to_metric_continuous R n A g hg) B hB.
change (@borel_set C B) in hPre.
exact (@borel_regular_borel_measurable R C (@hausdorff_measure R C n)
  (@hausdorff_measure_is_measure R C n) (@hausdorff_measure_borel_regular R C n) B hPre).
Qed.

(** Source for [riemannian_chart_inclusion_continuous]: the
    original inclusion into R^n is continuous in the rho
    topology, supporting 3.2.46, pp. 281–282. *)
Lemma riemannian_chart_inclusion_continuous : continuous (fun x : M=>(val x : E)).
Proof.
move=> x; exact (continuous_comp
  (@riemannian_metric_to_chart_continuous R n A g hg x)
  (@metric_subset_inclusion_continuous R E A (@riemannian_metric_to_chart R n A g hg x))).
Qed.

(** Source for [riemannian_chart_countable_open_base]: local
    arguments use a proved countable base in the actual rho
    topology, supporting 3.2.46, pp. 281–282. Empty and
    disconnected chart domains are included. *)
Lemma riemannian_chart_countable_open_base :
  exists U : nat -> set M, is_countable_open_base U.
Proof.
have [D [hCount hDense]] := @metric_subset_separable R E A (euclidean_metric_separable R n).
pose U := @SeparableMetricBase.value R C D hCount hDense.
have hBase := @SeparableMetricBase.laws R C D hCount hDense.
exists (fun i=>(@riemannian_metric_to_chart R n A g hg) @^-1` U i).
apply: (@homeomorphic_countable_base C M
  (@riemannian_chart_to_metric R n A g hg) (@riemannian_metric_to_chart R n A g hg) U).
- by move=> x.
- by move=> x.
- exact: riemannian_chart_to_metric_continuous.
- exact: riemannian_metric_to_chart_continuous.
- exact hBase.
Qed.
End Reference.
