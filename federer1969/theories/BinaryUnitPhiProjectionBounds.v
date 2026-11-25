(** Federer (1969), 3.3.20, p. 307: actual positive finite unit-refinement projection length. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalFamilyUP
  EqualCostIntervalSpecial SpecialIntervalFamilyUP PowerConcaveIntervalGauge BinaryCantorIntervalChildren
  BinaryCantorRatioBounds PlanarUnitSquareProjectionLength PlanarScalarSimilarityProjection
  AffineIntervalTransportUP AffineIntervalTransportExistence PositiveAffineClosedSegment
  PlanarAffineRectangleTransport EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanIntervalRectangles LebesgueScalarMeasure ScalarAffineLebesgue MeasureUP MeasureBasic RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_unit_phi_projection_bounds]: the
    actual unit-square refinement has projected length between
    lambda (|u_1|+|u_2|) and |u_1|+|u_2|, supporting the
    positive finite c_u in 3.3.20, p. 307. Its actual corner
    child supplies the lower bound; original child containment supplies
    the upper bound. All coefficient signs remain. *)
Theorem binary_original_unit_phi_projection_bounds (R:realType) (c m u v:R)
    (J:compact_real_intervals R) F:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) J 2 F ->
  let L:=lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
      (\bigcup_(P in [set` (F `*` F)%fset]) euclidean_interval_rectangle P.1 P.2)) in
  ((real_power 2 (-m^-1) * (`|u|+ `|v|))%R%:E<=L)%E /\(L<=(`|u|+ `|v|)%:E)%E.
Proof.
move=>hc hm hm1 hJ hF L.
pose s:=real_power (2:R) (-m^-1).
have hs:0<s:=(andP (binary_cantor_original_ratio_bounds hm hm1).1).1.
pose P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
  u * euclidean_real_plane_first p+v * euclidean_real_plane_second p.
pose C:=\bigcup_(D in [set` (F `*` F)%fset]) euclidean_interval_rectangle D.1 D.2.
have hSpecial:=@federer_2_10_28_4_special R _ (power_concave_interval_gauge hc hm hm1) J 2 F hF.
have hSubset:C `<=` euclidean_interval_rectangle J J.
  move=>x [D hD [hx0 hx1]].
  change (is_true (D \in (F `*` F)%fset)) in hD.
  move:hD;rewrite in_fsetM=>/andP[h0 h1].
  split;[exact:(special_interval_subsets hSpecial h0 hx0)|exact:(special_interval_subsets hSpecial h1 hx1)].
have hUpper:=measure_mono (lebesgue_scalar_is_measure R) (image_subset P hSubset).
rewrite (planar_original_unit_square_projection_length u v hJ) in hUpper.
have hInterval:is_compact_real_interval (`[0,s]:set (real_line_metric R)).
  exists 0,s;split=>//;exact:ltW hs.
pose K:compact_real_intervals R:=Sub (`[0,s]:set (real_line_metric R)) (mem_set hInterval).
have hK:K \in F.
  apply/(@binary_cantor_interval_children R c m 0 1 J F hc hm hm1 ltr01 hJ hF K).2.
  left;by rewrite subr0 mul1r add0r.
have hKK:euclidean_interval_rectangle K K `<=` C.
  move=>x hx;exists (K,K)=>//.
  by change (is_true ((K,K) \in (F `*` F)%fset));rewrite in_fsetM hK.
have [M hM]:=affine_interval_transport_exists 0 hs.
have hRoot:M J=K.
  apply:val_inj;by rewrite hM hJ positive_affine_closed_segment_image // !mulr0 !mulr1 !add0r.
have hSmall:=@planar_positive_affine_rectangle_transport R 0 0 s M M J J hM hM.
rewrite hRoot in hSmall.
have hProjection:lebesgue_scalar_measure (P @` euclidean_interval_rectangle K K)=
    (s * (`|u|+ `|v|))%R%:E.
  rewrite hSmall planar_scalar_original_similarity_projection.
  have hShift:(fun t:R=>u * 0+v * 0+s * t)=(fun t:R=>s * t+0) by apply:funext=>t;ring.
  by rewrite hShift scalar_affine_lebesgue_image ?gt_eqF // (ger0_norm (ltW hs))
    (planar_original_unit_square_projection_length u v hJ) -EFinM.
have hLower:=measure_mono (lebesgue_scalar_is_measure R) (image_subset P hKK).
rewrite hProjection in hLower.
by split.
Qed.
