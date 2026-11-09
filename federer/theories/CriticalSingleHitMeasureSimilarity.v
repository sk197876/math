(** Federer (1969), 3.3.20, p. 308: exact original psi scaling at the unique hit parent. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP EuclideanInnerProduct InnerMetric
  EuclideanRealPlane EuclideanIntervalRectangles BinaryCantorSingleHitSimilarity
  FiniteCellHitMeasureUP CriticalSquareHitMeasureUP RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_single_hit_measure_similarity]: the
    original hit measures satisfy psi_(j+k)(V)=4^(-j) psi_k(F^-1(V)),
    supporting the first-split reduction in 3.3.20, p. 308. Exact
    original counts and their literal weights prove the identity. *)
Theorem critical_original_single_hit_measure_similarity (R:realType) (c a b r:R)
    (J S T:compact_real_intervals R) H G psi (A:set (real_line_metric R)) j
    (V:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->0<r ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  is_critical_square_hit_measures G psi ->S \in H j ->T \in H j ->
  val S=(`[a,a+r]:set (real_line_metric R)) ->val T=(`[b,b+r]:set (real_line_metric R)) ->
  finite_cell_hit_indices (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) V=[fset (S,T)] ->
  let F:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>euclidean_real_plane_pair a b+r*:p in
  forall k,psi (j+k)%N V=((((4:R)^+j)^-1)%:E * psi k (F @^-1` V))%E.
Proof.
move=>hc hr hJ hTree hA hG hPsi hS hT hSV hTV hSingle F k.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have hCount:=@binary_cantor_single_hit_similarity_counts R c (1/2:R) a b r J S T H G A j V
  hc hm hm1 hr hJ hTree hA hG hS hT hSV hTV hSingle k.
rewrite !hPsi hCount -EFinM.
congr (_%:E);rewrite exprD invfM;ring.
Qed.
