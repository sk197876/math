(** Federer (1969), 3.3.21, p. 309: uniform actual point separation at every original interval level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  EqualCostIntervalTreeUP EqualCostIntervalSpecial EqualCostIntervalFamilyGap SpecialIntervalFamilyUP
  SpecialIntervalRefinement PowerConcaveIntervalGauge PowerCantorWidthLawsUP PowerCantorWidthExistence
  PowerCantorWidthBounds PowerCantorUniformGapScalar RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [power_cantor_original_level_point_gap]: distinct
    ACTUAL original intervals at level j have every pair of points
    separated by kappa*w_j, with kappa= 1-2*2^(-1/m)>0,
    supporting 3.3.21, p. 309. The same-parent case uses actual
    Phi spacing; the different-parent case uses the preceding level.
    No gap or growth premise is added to the original recursion. *)
Theorem power_cantor_original_level_point_gap (R:realType) (c m:R)
    (J:compact_real_intervals R) n H w:
  0<c ->0<m ->m<1 ->(forall j,(2<=n j)%N) ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_power_cantor_widths c m n w ->
  forall j (S T:compact_real_intervals R) (x y:real_line_metric R),
    S \in H j ->T \in H j ->S!=T ->val S x ->val T y ->
    (1-2 * real_power 2 (-m^-1)) * w j<=mdist x y.
Proof.
move=>hc hm hm1 hn hJ hTree hWidth.
pose k:= 1-2 * real_power (2:R) (-m^-1).
have hk:0<=k:=ltW (andP (power_cantor_uniform_gap_positive hm hm1)).1.
have hWidths:=@power_cantor_original_widths_identify R c m J n H w hc hm hm1 hJ hTree hWidth.
have hStep:=power_cantor_original_width_decreases hn hWidth.
elim=>[S T x y|j ih S T x y] hS hT hDifferent hx hy.
- have hSJ:S=J by move:hS;rewrite (equal_cost_tree_root hTree) in_fset1=>/eqP.
  have hTJ:T=J by move:hT;rewrite (equal_cost_tree_root hTree) in_fset1=>/eqP.
  by rewrite hSJ hTJ eqxx in hDifferent.
- have [F [hF hNext]]:=equal_cost_tree_step hTree j.
  rewrite hNext in hS hT.
  have [P [hP hSP]]:=(@special_interval_refinement_membership R (H j) F S).1 hS.
  have [Q [hQ hTQ]]:=(@special_interval_refinement_membership R (H j) F T).1 hT.
  have hxP:=special_interval_subsets
    (@federer_2_10_28_4_special R _ (power_concave_interval_gauge hc hm hm1) P (n j) (F P) (hF P hP)) hSP hx.
  have hyQ:=special_interval_subsets
    (@federer_2_10_28_4_special R _ (power_concave_interval_gauge hc hm hm1) Q (n j) (F Q) (hF Q hQ)) hTQ hy.
  case:(eqVneq P Q)=>hParents.
  + subst Q.
    have hPointGap:=@equal_cost_interval_family_point_gap R _ P (n j) (F P) S T x y
      (hF P hP) hSP hTQ hDifferent hx hy.
    have hSLevel:S \in H j.+1 by rewrite hNext;apply/special_interval_refinement_membership;by exists P.
    have hGap:=@power_cantor_original_child_gap_bounds R c m (w j) (w j.+1) (n j)
      hc hm hm1 (power_cantor_width_positive hWidth j) (hn j) (power_cantor_width_split hWidth j).
    rewrite (hWidths j P hP) (hWidths j.+1 S hSLevel) in hPointGap.
    exact:le_trans hGap.2 hPointGap.
  + have hPrevious:=ih P Q x y hP hQ hParents hxP hyQ.
    exact:le_trans (ler_wpM2l hk (hStep j)) hPrevious.
Qed.

(** Source for [power_cantor_original_sharp_next_level_gap]: every
    pair of points from distinct ACTUAL original level j+1 intervals
    is separated by kappa*w_j/n_j, supporting the sparse-radius
    argument of 3.3.21, p. 309. Previous parent gaps and current
    exact child spacing are both discharged. *)
Theorem power_cantor_original_sharp_next_level_gap (R:realType) (c m:R)
    (J:compact_real_intervals R) n H w j (S T:compact_real_intervals R) (x y:real_line_metric R):
  0<c ->0<m ->m<1 ->(forall j,(2<=n j)%N) ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J n H ->
  is_power_cantor_widths c m n w ->
  S \in H j.+1 ->T \in H j.+1 ->S!=T ->val S x ->val T y ->
  (1-2 * real_power 2 (-m^-1)) * w j/(n j)%:R<=mdist x y.
Proof.
move=>hc hm hm1 hn hJ hTree hWidth hS hT hDifferent hx hy.
pose k:= 1-2 * real_power (2:R) (-m^-1).
have hk:0<k:=(andP (power_cantor_uniform_gap_positive hm hm1)).1.
have hW:=power_cantor_width_positive hWidth j.
have hN1:1<((n j)%:R:R) by rewrite ltr1n.
have hN:0<((n j)%:R:R):=lt_trans ltr01 hN1.
have hWidths:=@power_cantor_original_widths_identify R c m J n H w hc hm hm1 hJ hTree hWidth.
have [F [hF hNext]]:=equal_cost_tree_step hTree j.
have [P [hP hSP]]:=(special_interval_refinement_membership (H j) F S).1 (ltac:(by rewrite -hNext)).
have [Q [hQ hTQ]]:=(special_interval_refinement_membership (H j) F T).1 (ltac:(by rewrite -hNext)).
case:(eqVneq P Q)=>hParents.
- subst Q.
  have hPointGap:=@equal_cost_interval_family_point_gap R _ P (n j) (F P) S T x y
    (hF P hP) hSP hTQ hDifferent hx hy.
  rewrite (hWidths j P hP) (hWidths j.+1 S hS) in hPointGap.
  have hGap:=@power_cantor_original_child_gap_bounds R c m (w j) (w j.+1) (n j)
    hc hm hm1 hW (hn j) (power_cantor_width_split hWidth j).
  exact:le_trans hGap.1 hPointGap.
- have hxP:=special_interval_subsets
    (@federer_2_10_28_4_special R _ (power_concave_interval_gauge hc hm hm1) P (n j) (F P) (hF P hP)) hSP hx.
  have hyQ:=special_interval_subsets
    (@federer_2_10_28_4_special R _ (power_concave_interval_gauge hc hm hm1) Q (n j) (F Q) (hF Q hQ)) hTQ hy.
  have hPrevious:=@power_cantor_original_level_point_gap R c m J n H w
    hc hm hm1 hn hJ hTree hWidth j P Q x y hP hQ hParents hxP hyQ.
  have hSmaller:k * w j/(n j)%:R<=k * w j.
    rewrite ler_pdivrMr //;have hkw:0<=k * w j:=mulr_ge0 (ltW hk) (ltW hW);nra.
  exact:le_trans hSmaller hPrevious.
Qed.
