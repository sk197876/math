(** Federer (1969), 3.3.20, p. 308: exact actual hit counts in the first-split similarity. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP EuclideanInnerProduct InnerMetric
  EuclideanRealPlane EuclideanIntervalRectangles BinaryCantorSingleHitDescendants
  BinaryCantorSquareDescendantSimilarity PlanarAffineRectangleTransport
  FiniteCellHitMeasureUP FiniteCellHitImage RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_single_hit_similarity_counts]: the
    initial similarity reduction preserves the literal original finer
    hit counts, 3.3.20, p. 308. Every hit lies in the unique original
    parent, whose actual descendant family is transported by its positive
    plane similarity. Arbitrary original test sets are retained. *)
Theorem binary_cantor_single_hit_similarity_counts (R:realType) (c m a b r:R)
    (J S T:compact_real_intervals R) H G (A:set (real_line_metric R)) j
    (V:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->0<m ->m<1 ->0<r ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  S \in H j ->T \in H j ->
  val S=(`[a,a+r]:set (real_line_metric R)) ->val T=(`[b,b+r]:set (real_line_metric R)) ->
  finite_cell_hit_indices (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) V=[fset (S,T)] ->
  let F:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>euclidean_real_plane_pair a b+r*:p in
  forall k,#|` finite_cell_hit_indices (G (j+k)%N)
      (fun P=>euclidean_interval_rectangle P.1 P.2) V|=
    #|` finite_cell_hit_indices (G k)
      (fun P=>euclidean_interval_rectangle P.1 P.2) (F @^-1` V)|.
Proof.
move=>hc hm hm1 hr hJ hTree hA hG hS hT hSV hTV hSingle F k.
have [M [N [hM [hN [hInjective hFamilies]]]]]:=
  @binary_cantor_original_descendant_square_similarity R c m a b r J S T H G A j
  hc hm hm1 hr hJ hTree hA hG hS hT hSV hTV.
rewrite (@binary_cantor_single_hit_original_descendants R c m J S T H G j V
  hc hm hm1 hTree hG hSingle k) (hFamilies k).
apply:(@finite_cell_hit_image_cardinality _ _ _ _ (G k)
  (fun P:compact_real_intervals R*compact_real_intervals R=>(M P.1,N P.2)) F
  (fun P=>euclidean_interval_rectangle P.1 P.2)
  (fun P=>euclidean_interval_rectangle P.1 P.2) V hInjective).
move=>P _;exact:planar_positive_affine_rectangle_transport hM hN.
Qed.
