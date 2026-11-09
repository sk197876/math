(** Federer (1969), 3.3.20, p. 307: a positive uniform projection coefficient for every actual square. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalFamilyUP
  BinaryUnitPhiProjectionBounds BinarySquarePhiProjectionScale PlanarUnitSquareProjectionLength
  AffineIntervalTransportUP AffineIntervalTransportExistence PositiveAffineClosedSegment
  PlanarAffineRectangleTransport PlanarScalarSimilarityProjection ScalarAffineLebesgue
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanIntervalRectangles
  LebesgueScalarMeasure RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_uniform_projection_coefficient]:
    for every original unit direction there is 0<c_u<=1 such that
    EVERY nondegenerate original square's actual Phi refinement has
    projected volume c_u times its own projection volume, 3.3.20,
    p. 307. The coefficient is derived from positive finite actual
    unit-refinement length; original Phi similarity proves uniformity.
    The false c_u<1 nullity assertion deleted by the published
    erratum is neither stated nor used. *)
Theorem binary_original_uniform_projection_coefficient (R:realType) (c m u v:R)
    (J:compact_real_intervals R) F:
  0<c ->0<m ->m<1 ->u^+2+v^+2= 1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) J 2 F ->
  exists cu:R,0<cu /\cu<=1 /\forall (a b r:R) (S T:compact_real_intervals R) FS FT,
    0<r ->val S=(`[a,a+r]:set (real_line_metric R)) ->val T=(`[b,b+r]:set (real_line_metric R)) ->
    is_equal_cost_interval_family (fun t=>c * real_power t m) S 2 FS ->
    is_equal_cost_interval_family (fun t=>c * real_power t m) T 2 FT ->
    lebesgue_scalar_measure
      ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
        u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
        (\bigcup_(P in [set` (FS `*` FT)%fset]) euclidean_interval_rectangle P.1 P.2))=
      (cu%:E * lebesgue_scalar_measure
      ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
        (u * euclidean_real_plane_first p+v * euclidean_real_plane_second p)%R) @`
        euclidean_interval_rectangle S T))%E.
Proof.
move=>hc hm hm1 hUnit hJ hF.
pose P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
  u * euclidean_real_plane_first p+v * euclidean_real_plane_second p.
pose W:=(`|u|+ `|v|).
have hW:0<W.
  have hu:=normr_ge0 u;have hv:=normr_ge0 v.
  have hAbs:`|u|^+2 + `|v|^+2= 1 by rewrite -!normrX !ger0_norm ?sqr_ge0.
  rewrite /W;case:(ltP 0 (`|u|+ `|v|))=>// hNo;nra.
pose L:=lebesgue_scalar_measure
  (P @` (\bigcup_(D in [set` (F `*` F)%fset]) euclidean_interval_rectangle D.1 D.2)).
have [hLower hUpper]:=@binary_original_unit_phi_projection_bounds R c m u v J F hc hm hm1 hJ hF.
change (is_true (((real_power 2 (-m^-1) * W)%R%:E<=L)%E)) in hLower.
change (is_true ((L<=W%:E)%E)) in hUpper.
have hLambda:0<real_power (2:R) (-m^-1) by apply:real_power_strictly_positive;by rewrite ltr0n.
case hValue:L hLower hUpper=>[l| |] hLower hUpper;last 2 first.
- by rewrite leye_eq in hUpper.
- by [].
have hL:0<l.
  move:hLower;rewrite lee_fin=>hLower;exact:lt_le_trans (mulr_gt0 hLambda hW) hLower.
have hLW:l<=W by move:hUpper;rewrite lee_fin.
pose cu:=l/W.
have hCU:0<cu by rewrite /cu divr_gt0.
have hCU1:cu<=1 by rewrite /cu ler_pdivrMr // mul1r.
have hIdentity:cu * W=l by rewrite /cu divfK ?gt_eqF.
exists cu;split=>//;split=>//;move=>a b r S T FS FT hr hS hT hFS hFT.
rewrite (@binary_original_square_phi_projection_scale R c m a b r u v J S T F FS FT
  hc hm hm1 hr hJ hS hT hF hFS hFT).
change ((r%:E * L)%E=(cu%:E * lebesgue_scalar_measure (P @` euclidean_interval_rectangle S T))%E).
have [M hM]:=affine_interval_transport_exists a hr.
have [N hN]:=affine_interval_transport_exists b hr.
have hMS:M J=S.
  apply:val_inj;by rewrite hM hJ positive_affine_closed_segment_image // !mulr0 !mulr1 !addr0 -hS.
have hNT:N J=T.
  apply:val_inj;by rewrite hN hJ positive_affine_closed_segment_image // !mulr0 !mulr1 !addr0 -hT.
have hRoot:=@planar_positive_affine_rectangle_transport R a b r M N J J hM hN.
rewrite hMS hNT in hRoot.
have hMass:lebesgue_scalar_measure (P @` euclidean_interval_rectangle S T)=(r * W)%R%:E.
  rewrite hRoot planar_scalar_original_similarity_projection.
  have hShift:(fun t:R=>u * a+v * b+r * t)=(fun t:R=>r * t+(u * a+v * b))
    by apply:funext=>t;ring.
  by rewrite hShift scalar_affine_lebesgue_image ?gt_eqF // (ger0_norm (ltW hr))
    (planar_original_unit_square_projection_length u v hJ) -EFinM.
rewrite hValue hMass -!EFinM.
apply:congr1;rewrite -hIdentity;ring.
Qed.
