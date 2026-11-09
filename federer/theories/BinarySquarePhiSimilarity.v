(** Federer (1969), 3.3.20, p. 307: the same unit refinement under every original square similarity. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalFamilyUP
  PowerConcaveIntervalGauge PowerCantorFamilyAffineTransport AffineIntervalTransportUP
  AffineIntervalTransportExistence PositiveAffineClosedSegment FiniteCartesianImage FiniteCellUnionImage
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanIntervalRectangles
  PlanarAffineRectangleTransport RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_square_phi_similarity]: the ACTUAL
    Phi refinement of every nondegenerate original square is the
    translated positive similarity of the unit-square refinement,
    supporting the single c_u for all T in 3.3.20, p. 307.
    Original Phi laws and uniqueness prove the identity; interval
    transports remain local existence witnesses behind their laws. *)
Theorem binary_original_square_phi_similarity (R:realType) (c m a b r:R)
    (J S T:compact_real_intervals R) F FS FT:
  0<c ->0<m ->m<1 ->0<r ->val J=(`[0,1]:set (real_line_metric R)) ->
  val S=(`[a,a+r]:set (real_line_metric R)) ->val T=(`[b,b+r]:set (real_line_metric R)) ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) J 2 F ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) S 2 FS ->
  is_equal_cost_interval_family (fun t=>c * real_power t m) T 2 FT ->
  (\bigcup_(P in [set` (FS `*` FT)%fset]) euclidean_interval_rectangle P.1 P.2)=
    (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>euclidean_real_plane_pair a b+r*:p) @`
      (\bigcup_(P in [set` (F `*` F)%fset]) euclidean_interval_rectangle P.1 P.2).
Proof.
move=>hc hm hm1 hr hJ hS hT hF hFS hFT.
have [M hM]:=affine_interval_transport_exists a hr.
have [N hN]:=affine_interval_transport_exists b hr.
have hRootM:M J=S.
  apply:val_inj;by rewrite hM hJ positive_affine_closed_segment_image //
    !mulr0 !mulr1 !addr0 -hS.
have hRootN:N J=T.
  apply:val_inj;by rewrite hN hJ positive_affine_closed_segment_image //
    !mulr0 !mulr1 !addr0 -hT.
have hFM:=@power_cantor_family_positive_affine_transport R a r c m M J 2 F hr hM hF.
have hFN:=@power_cantor_family_positive_affine_transport R b r c m N J 2 F hr hN hF.
rewrite hRootM in hFM;rewrite hRootN in hFN.
have hFSImage:=@equal_cost_interval_family_unique R _ (power_concave_interval_gauge hc hm hm1)
  S 2 FS _ hFS hFM.
have hFTImage:=@equal_cost_interval_family_unique R _ (power_concave_interval_gauge hc hm hm1)
  T 2 FT _ hFT hFN.
rewrite hFSImage hFTImage finite_cartesian_image.
apply:finite_cell_union_image=>P hP.
exact:planar_positive_affine_rectangle_transport hM hN.
Qed.
