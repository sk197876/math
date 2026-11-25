(** Federer (1969), 3.3.20, p. 308:
    actual singleton counterexample to unqualified finite-stage attainment. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EqualCostFirstEndpoint BinaryCantorSquareLevelsUP CriticalSquareHitMeasureUP
  FiniteCellHitPointPositive EuclideanInnerProduct InnerMetric EuclideanRealPlane
  MetricCartesianProductUP EuclideanIntervalRectangles MetricDiameter MetricDiameterMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_square_original_singleton_qualification]:
    local counterexample to the auxiliary assertion that
    every S has diam(S)>=psi_j(S) for some
    j in 3.3.20, p. 308. The original
    corner (0,0) lies in a level square at
    every level. Its singleton has diameter zero
    and strictly positive finite-stage hit mass. This
    qualifies finite-stage attainment only; it does not
    alter the numbered Hausdorff-measure conclusion and is
    absent from the published erratum. *)
Theorem critical_square_original_singleton_qualification (R:realType) (h:R->R)
    (J:compact_real_intervals R) n H G psi:
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree h J n H ->
  is_binary_cantor_square_levels H G ->is_critical_square_hit_measures G psi ->
  let z:=@euclidean_real_plane_pair R 0 0 in
  extended_metric_diameter [set z]=0 /\forall j,(0<psi j [set z])%E.
Proof.
move=>hJ hTree hG hPsi z;split;first exact:extended_metric_diameter_singleton.
move=>j.
have [S [hS [d [hd hValue]]]]:=@equal_cost_tree_first_endpoint R h J n H 0 1 hJ ltr01 hTree j.
have hMember:(S,S) \in G j by rewrite hG in_fsetM hS.
have hPoint:euclidean_interval_rectangle S S z.
  change (val S (euclidean_real_plane_first (@euclidean_real_plane_pair R 0 0)) /\
    val S (euclidean_real_plane_second (@euclidean_real_plane_pair R 0 0))).
  rewrite
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  split;rewrite hValue /=;apply/andP;split;[exact:lexx|exact:ltW hd|exact:lexx|exact:ltW hd].
apply:(@finite_cell_hit_point_positive R _ _ (G j)
  (fun P=>euclidean_interval_rectangle P.1 P.2) (Num.sqrt 2/(4:R)^+j) (psi j) z (hPsi j)).
- apply:divr_gt0;[by rewrite sqrtr_gt0 ltr0n|by rewrite exprn_gt0 // ltr0n].
- exists (S,S);by split.
Qed.
