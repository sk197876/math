(** Federer (1969), 3.3.20, pp. 306–308:
    the actual original square count is four to the level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorSquareLevelsUP BinaryCantorLevelCounts FiniteCartesianFamilyCardinality RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_original_square_count]: exact
    card(G_j)=4^j in 3.3.20, pp. 306–308.
    Actual factor counts and the independently specified
    Cartesian level laws give the count, including j=0. *)
Theorem binary_cantor_original_square_count (R:realType) (c m:R)
    (J:compact_real_intervals R) H G:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->forall j,#|` G j|=(4^j)%N.
Proof.
move=>hc hm hm1 hJ hTree hG j.
have hCount:=@binary_cantor_level_count R c m J H hc hm hm1 hJ hTree j.
by rewrite (hG j) finite_cartesian_family_cardinality hCount -expnMn.
Qed.
