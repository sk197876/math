(** Federer (1969), 3.2.36, p. 273:
    bounded Euclidean tube factors meet the
    actual rectifiability hypotheses of 3.2.23. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric CoveringFamilyUP
  EuclideanLipschitzRectifiableImage RectifiableSetUP RectifiableFiniteHausdorffMass LipschitzUP
  CompactSetDistanceProfile CompactHausdorffMetric CompactMetricBounded EuclideanDistanceTubeBasic
  HausdorffMeasure TopologicalBorel MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bounded_identity_rectifiable]:
    supporting the second-factor rectifiability
    needed in Federer 3.2.36, p. 273,
    from 3.2.14(1), pp. 251--252.
    Every bounded subset of R^n is
    genuinely n-rectifiable by its identity
    parametrization. No measurability is needed;
    n=0 retains its finite-set convention. *)
Lemma euclidean_bounded_identity_rectifiable (R:realType) n
    (A:set (inner_metric_space (@euclidean_inner_productP R n))):
  metric_set_bounded A ->is_m_rectifiable n A.
Proof.
move=>hBound.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
have hIdentity:@is_metric_lipschitz R X X A (@id X).
  exists 1; split; first exact:ltr01.
  split; first exact:ler01.
  by move=>x y _ _; rewrite mul1r.
have hRect:=euclidean_lipschitz_bounded_image_rectifiable hBound hIdentity.
by rewrite image_id in hRect.
Qed.

(** Source for [compact_distance_tube_rectifiable]: supporting
    the actual second-factor tube in the
    3.2.23 application of Federer 3.2.36,
    p. 273. Distance laws prove openness
    and boundedness; the actual identity map
    gives genuine ambient-degree rectifiability
    and its proved finite Hausdorff mass.
    Every natural dimension, including the
    positive zero-dimensional atom, remains. *)
Theorem compact_distance_tube_rectifiable (R:realType) n
    (B:compact_hausdorff_space (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  0<r ->
  is_m_rectifiable n [set y|compact_set_distance_profile B y<r] /\
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) [set y|compact_set_distance_profile B y<r] /\
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) n) n [set y|compact_set_distance_profile B y<r].
Proof.
move=>hr.
have hD:=compact_set_distance_profile_specification B.
have hBound:=@euclidean_distance_tube_bounded R n (val B) (compact_set_distance_profile B) r
  (set_valP B).2 hD (compact_metric_diameter_finite B) hr.
have hRect:=euclidean_bounded_identity_rectifiable hBound.
split; first exact:hRect.
split.
- apply:open_borel_set; exact:(@euclidean_distance_tube_open R n (val B) (compact_set_distance_profile B) r hD).
- exact:rectifiable_hausdorff_measure_rectifiable hRect.
Qed.
