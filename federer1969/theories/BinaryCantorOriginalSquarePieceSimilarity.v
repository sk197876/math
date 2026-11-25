(** Federer (1969), 3.3.20, p. 307: exact original Cantor-square pieces under positive similarities. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorOriginalPieceSimilarity BinaryCantorSquareCoordinates
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles
  PlanarAffineProductImage RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_original_square_piece_similarity]:
    each actual T intersect E is an exact translated, positively scaled
    copy of the original E, as used in the Borel partitions of
    3.3.20, p. 307. Original factor recursion, exact restricted limit
    identities and actual plane coordinate laws prove the set identity;
    no self-similarity or projection scaling is assumed. *)
Theorem binary_cantor_original_square_piece_similarity (R:realType) (c m:R)
    (J S T:compact_real_intervals R) H (A:set (real_line_metric R)) j:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->S \in H j ->T \in H j ->
  let r:=(real_power 2 (-m^-1))^+j in
  exists a b:R,euclidean_cantor_product A A `&` euclidean_interval_rectangle S T=
    (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>euclidean_real_plane_pair a b+r*:p) @`
      euclidean_cantor_product A A.
Proof.
move=>hc hm hm1 hJ hTree hA hS hT r.
have [a [b [hSV hTV]]]:=@binary_cantor_original_square_coordinates R c m J S T H j
  hc hm hJ hTree hS hT.
have hTwo:(0<2:>R) by rewrite ltr0n.
have hr:0<r by rewrite /r exprn_gt0 //;exact:real_power_strictly_positive.
have [_ [_ [_ hLeft]]]:=@binary_cantor_original_piece_similarity R c m a r J S H A j
  hc hm hm1 hr hJ hTree hA hS hSV.
have [_ [_ [_ hRight]]]:=@binary_cantor_original_piece_similarity R c m b r J T H A j
  hc hm hm1 hr hJ hTree hA hT hTV.
exists a,b;rewrite planar_affine_original_product_image hLeft hRight.
apply/seteqP;split=>x.
- move=>[[hxA hyA] [hxS hyT]];by split;split.
- move=>[[hxA hxS] [hyA hyT]];by split;split.
Qed.
