(** Federer (1969), 3.3.20, p. 307: the actual c_u=1 locus is precisely the full first projection. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalFamilyUP
  EqualCostIntervalSpecial SpecialIntervalFamilyUP PowerConcaveIntervalGauge
  PlanarUnitSquareProjectionLength PlanarScalarProjectionContinuity BinaryCantorSquareLevelTopology
  ClosedIntervalFullProjectionMass EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanIntervalRectangles LebesgueScalarMeasure RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_coefficient_one_full_projection]:
    c_u=1 if and only if the ACTUAL original first refinement fills
    the root projection, identifying U on p. 307 of 3.3.20.
    The coefficient is specified only by its actual normalized
    projected-length equation; existence and uniformity are already
    proved separately. Compactness and the proved closed-interval
    full-mass criterion exclude any missing gap. *)
Theorem binary_original_coefficient_one_full_projection (R:realType) (c m u v cu:R)
    (J:compact_real_intervals R) F:
  0<c ->0<m ->m<1 ->u^+2+v^+2= 1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) J 2 F ->
  let P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p in
  let C:=\bigcup_(D in [set` (F `*` F)%fset]) euclidean_interval_rectangle D.1 D.2 in
  lebesgue_scalar_measure (P @` C)=(cu * (`|u|+ `|v|))%R%:E ->
  (cu= 1 <->P @` C= P @` euclidean_interval_rectangle J J).
Proof.
move=>hc hm hm1 hUnit hJ hF P C hCoefficient.
pose W:=(`|u|+ `|v|).
pose a:=(u-`|u|+v-`|v|)/2.
have hW:0<W.
  have hu:=normr_ge0 u;have hv:=normr_ge0 v.
  have hAbs:`|u|^+2 + `|v|^+2= 1 by rewrite -!normrX !ger0_norm ?sqr_ge0.
  rewrite /W;case:(ltP 0 (`|u|+ `|v|))=>// hNo;nra.
have hEndpoints:a<a+W by lra.
have hRoot:P @` euclidean_interval_rectangle J J=(`[a,a+W]:set (real_line_metric R)).
  rewrite (planar_original_unit_square_projection_interval u v hJ).
  congr (`[_,_]:set (real_line_metric R));rewrite /a /W;by rewrite addrA.
have hSpecial:=@federer_2_10_28_4_special R _ (power_concave_interval_gauge hc hm hm1) J 2 F hF.
have hSubset:C `<=` euclidean_interval_rectangle J J.
  move=>x [D hD [hx0 hx1]].
  change (is_true (D \in (F `*` F)%fset)) in hD.
  move:hD;rewrite in_fsetM=>/andP[h0 h1].
  split;[exact:(special_interval_subsets hSpecial h0 hx0)|exact:(special_interval_subsets hSpecial h1 hx1)].
have hProjectionSubset:P @` C `<=` `[a,a+W] by rewrite -hRoot;exact:(image_subset P hSubset).
have hCompact:=@original_square_level_union_compact R (F `*` F)%fset.
have hContinuous:=@planar_scalar_original_projection_continuous R u v.
have hCompactProjection:compact (P @` C : set (real_line_metric R)):=continuous_compact (continuous_subspaceT hContinuous) hCompact.
have hClosedProjection:=compact_closed (@metric_hausdorff R [the metricType R of real_line_metric R]) hCompactProjection.
have hCriterion:=@closed_interval_subset_full_length R a (a+W) (P @` C)
  hEndpoints hClosedProjection hProjectionSubset.
have hLength:(a+W)-a=W by lra.
rewrite hLength in hCriterion.
split.
- move=>hOne;rewrite hRoot;apply:hCriterion.1.
  by rewrite hCoefficient hOne mul1r.
- move=>hEqual.
  have hMass:=congr1 (@lebesgue_scalar_measure R) hEqual.
  rewrite hCoefficient (planar_original_unit_square_projection_length u v hJ) in hMass.
  have hScalar:cu * W=W by apply:(@EFin_inj R);exact:hMass.
  have h:=congr1 (fun t:R=>t/W) hScalar.
  by rewrite mulfK ?gt_eqF // divff ?gt_eqF // in h.
Qed.
