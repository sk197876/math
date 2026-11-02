(** Federer (1969), 3.2.34, p. 271: Rademacher
    and the nearest-segment differential calculation make
    the actual distance Jacobian equal to one almost
    everywhere in every positive-distance strip. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanOneCoordinate MetricSetDistanceUP MetricSetDistanceBasic EuclideanDistanceLipschitz
  EuclideanClosedDistanceJacobian NormDifferentialUP Jacobian
  EuclideanTargetJacobianMeasurable PartialFunctionUP PartialFunctionPostcomposition
  EuclideanLebesgueDimensions MeasureUP MeasureAlmostUP MeasureAlmostBasic Rademacher
  ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_distance_jacobian_one_almost]:
    the removal of the Jacobian from the coarea source
    integral in Federer 3.2.34, p. 271. Its
    original partial differential domain remains; no arbitrary
    values at exceptional points are chosen. The case a=0
    is retained. *)
Lemma euclidean_distance_jacobian_one_almost (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) d a b:
  closed S ->S!=set0 ->is_metric_set_distance S d ->0<=a ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R n)
    [set x|a<d x<b] [set x|partial_function_graph
      (extended_euclidean_target_jacobian (fun z=>euclidean_one_embed (d z))) x (1%R)%:E].
Proof.
move=>hClosed hNonempty hDistance ha.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono (euclidean_lebesgue_is_measure R n) _
  (federer_3_1_6 (euclidean_distance_lipschitz hDistance))).
move=>x [L hD] /andP[hax hxb].
have hx:~S x.
  move=>hS; have he:=metric_set_distance_member hDistance hS.
  rewrite he in hax; have hBad:=le_lt_trans ha hax; by rewrite ltxx in hBad.
exists (1:R); split=>//.
apply:(euclidean_jacobian_graph 1 setT (fun z=>euclidean_one_embed (d z)) x 1).2.
exists L; split; first exact hD.
exact:(euclidean_closed_distance_jacobian_one hClosed hNonempty hDistance hx hD).
Qed.
