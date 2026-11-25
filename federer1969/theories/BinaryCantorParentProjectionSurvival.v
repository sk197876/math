(** Federer (1969), 3.3.20, p. 307: original parent projections survive refinement. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP SpecialIntervalFamilyBasic BinaryCantorSquareLevelsUP
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanIntervalRectangles
  BinaryCantorSquareCoordinates BinaryCantorSquareDescendantSimilarity AffineIntervalTransportUP
  PlanarAffineRectangleTransport PlanarScalarSimilarityProjection FiniteCellUnionImage
  EuclideanRectangleScalarProjection PositiveAffineClosedSegment RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_parent_projection_survival]: once the
    actual first-level projection fills its parent interval, every
    original parent's projection survives the next actual refinement,
    3.3.20, p. 307. The actual descendant-square similarity and scalar
    projection transport discharge the local self-similarity step. *)
Theorem binary_original_parent_projection_survival (R:realType) (c m u v:R)
    (J:compact_real_intervals R) H G (A:set (real_line_metric R)):
  0<c ->0<m ->m<1 ->0<=u ->0<=v ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  let P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p in
  P @` (\bigcup_(D in [set` G 1%N]) euclidean_interval_rectangle D.1 D.2)=(`[0,u+v]:set R) ->
  forall j S T,S \in H j ->T \in H j ->
    P @` euclidean_interval_rectangle S T `<=`
    P @` (\bigcup_(D in [set` G j.+1]) euclidean_interval_rectangle D.1 D.2).
Proof.
move=>hc hm hm1 hu hv hJ hTree hA hG P hFull j S T hS hT.
have [a [b [hSV hTV]]]:=@binary_cantor_original_square_coordinates R c m J S T H j
  hc hm hJ hTree hS hT.
pose r:=(real_power (2:R) (-m^-1))^+j.
have hTwo:(0<2:>R) by rewrite ltr0n.
have hr:0<r by rewrite /r exprn_gt0 //;exact:real_power_strictly_positive.
have [M [N [hM [hN [hInjective hFamilies]]]]]:=
  @binary_cantor_original_descendant_square_similarity R c m a b r J S T H G A j
  hc hm hm1 hr hJ hTree hA hG hS hT hSV hTV.
pose K:=((special_interval_restriction (H j.+1) (val S)) `*`
  (special_interval_restriction (H j.+1) (val T)))%fset.
have hFamily:K=[fset (M D.1,N D.2)|D in G 1%N].
  have h:=hFamilies 1%N;by rewrite addn1 in h.
have hUnion:(\bigcup_(D in [set` K]) euclidean_interval_rectangle D.1 D.2)=
    (fun x:inner_metric_space (@euclidean_inner_productP R 2)=>euclidean_real_plane_pair a b+r*:x) @`
      (\bigcup_(D in [set` G 1%N]) euclidean_interval_rectangle D.1 D.2).
  rewrite hFamily;apply:finite_cell_union_image=>D _.
  exact:planar_positive_affine_rectangle_transport hM hN.
have hImage:P @` (\bigcup_(D in [set` K]) euclidean_interval_rectangle D.1 D.2)=
    (`[u * a+v * b,u * (a+r)+v * (b+r)]:set R).
  rewrite hUnion planar_scalar_original_similarity_projection hFull positive_affine_closed_segment_image //.
  have hLeft:u * a+v * b+r * 0=u * a+v * b by ring.
  have hRight:u * a+v * b+r * (u+v)=u * (a+r)+v * (b+r) by ring.
  by rewrite hLeft hRight.
have hParentImage:P @` euclidean_interval_rectangle S T=
    (`[u * a+v * b,u * (a+r)+v * (b+r)]:set R).
  exact:(@euclidean_rectangle_scalar_projection R S T a (a+r) b (b+r) u v
    (ltac:(lra)) (ltac:(lra)) hu hv hSV hTV).
move=>z hz;rewrite -hParentImage in hImage.
have hzK:(P @` (\bigcup_(D in [set` K]) euclidean_interval_rectangle D.1 D.2)) z
  by rewrite hImage.
have [x [D hD hx] hValue]:=hzK.
have hDM:=hD;change (is_true (D \in K)) in hDM.
rewrite /K in_fsetM in hDM.
move:hDM=>/andP[/special_interval_restriction_membership[hD0 _]
  /special_interval_restriction_membership[hD1 _]].
exists x=>//;exists D;first by change (is_true (D \in G j.+1));rewrite hG in_fsetM hD0 hD1.
exact:hx.
Qed.
