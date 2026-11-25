(** Federer (1969), 3.3.20, p. 308: refinement bound for the actual original square hit count. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EqualCostIntervalSpecial SpecialIntervalFamilyUP SpecialIntervalRefinement PowerConcaveIntervalGauge
  BinaryCantorSquareLevelsUP EqualCostIntervalFamilyCount FiniteCartesianFamilyCardinality
  FiniteFsetUnionCardBound FiniteCellHitMeasureUP FiniteCellHitIndicesLaws
  EuclideanInnerProduct InnerMetric EuclideanIntervalRectangles RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_square_hit_refinement_count]: each
    original parent square has four children, and every child hit
    forces a parent hit. Thus the actual next hit count is at most
    four times the preceding count, supporting psi_j>=psi_(j+1)
    in 3.3.20, p. 308. No selected global parent is used. *)
Theorem binary_original_square_hit_refinement_count (R:realType) (c m:R)
    (J:compact_real_intervals R) H G j
    (V:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->0<m ->m<1 ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->
  (#|` finite_cell_hit_indices (G j.+1) (fun P=>euclidean_interval_rectangle P.1 P.2) V|<=
    4 * #|` finite_cell_hit_indices (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) V|)%N.
Proof.
move=>hc hm hm1 hTree hG.
have [K [hK hNext]]:=equal_cost_tree_step hTree j.
pose hits:=finite_cell_hit_indices (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) V.
pose children (P:compact_real_intervals R*compact_real_intervals R):=
  (K P.1 `*` K P.2)%fset.
have hCount P:P \in hits ->#|` children P|=4%N.
  move=>/finite_cell_hit_indices_membership[hP _].
  move:hP;rewrite hG in_fsetM=>/andP[hS hT].
  by rewrite /children finite_cartesian_family_cardinality
    (equal_cost_original_interval_family_count (hK _ hS))
    (equal_cost_original_interval_family_count (hK _ hT)).
have hSubset:(finite_cell_hit_indices (G j.+1)
    (fun P=>euclidean_interval_rectangle P.1 P.2) V `<=`
    (\bigcup_(P<-hits) children P))%fset.
  apply/fsubsetP=>P;case:P=>S T /finite_cell_hit_indices_membership[hP [x [[hxS hxT] hxV]]].
  move:hP;rewrite hG in_fsetM hNext=>/andP[hS hT].
  have [P [hP hSP]]:=(@special_interval_refinement_membership R (H j) K S).1 hS.
  have [Q [hQ hTQ]]:=(@special_interval_refinement_membership R (H j) K T).1 hT.
  have hSpecialP:=@federer_2_10_28_4_special R _ (power_concave_interval_gauge hc hm hm1)
    P 2 (K P) (hK P hP).
  have hSpecialQ:=@federer_2_10_28_4_special R _ (power_concave_interval_gauge hc hm hm1)
    Q 2 (K Q) (hK Q hQ).
  have hxP:=special_interval_subsets hSpecialP hSP hxS.
  have hxQ:=special_interval_subsets hSpecialQ hTQ hxT.
  apply/bigfcupP;exists (P,Q);last by rewrite /children in_fsetM hSP hTQ.
  apply/andP;split;last by [].
  apply/finite_cell_hit_indices_membership;split.
  - by rewrite hG in_fsetM hP hQ.
  - exists x;by split;[split|].
apply:leq_trans (fsubset_leq_card hSubset) _.
apply:leq_trans (finite_fset_union_card_upper hits children) _.
have hSum:(\sum_(P<-hits) #|` children P|=\sum_(P<-hits) 4)%N.
  apply:eq_big_seq=>P hP;exact:hCount P hP.
rewrite hSum big_seq_fsetE sum_nat_const cardT -cardE -cardfE mulnC.
exact:leqnn.
Qed.
