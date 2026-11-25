(** Federer (1969), 3.2.40, p. 276: obtain an
    actual separated finite subset of the original Cantor
    square at each finite interval level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge RealPower
  RapidPowerCantorScalesUP EqualCostIntervalTreeUP SpecialIntervalFamilyUP
  CantorLevelPointSelection SubcriticalCantorTreeGap CantorSplitRadius
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct
  MetricCartesianProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cantor_level_selected_points_separated]: supporting
    actual point separation for Federer 3.2.40, p. 276.
    Independent selection laws and actual interval gaps prove
    the bound; it is not an additional selection premise. *)
Lemma cantor_level_selected_points_separated (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R) (J:compact_real_intervals R) (H:nat->{fset compact_real_intervals R})
    (A:set (real_line_metric R)) (j:nat)
    (v:'I_(size (H j.+1:seq (compact_real_intervals R)))->real_line_metric R):
  0<c ->0<m ->m<=1/2 ->is_rapid_power_cantor_scales c m n s ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  @is_interval_level_point_selection R J (H j.+1) A v ->forall i k,i!=k ->
  cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1<=mdist (v i) (v k).
Proof.
move=>hc hm hmHalf hScales hJ hTree hV i k hDifferent.
have hMember (t:'I_(size (H j.+1:seq (compact_real_intervals R)))):nth J (H j.+1) t \in H j.+1:=mem_nth J (ltn_ord t).
have hIntervals:nth J (H j.+1) i!=nth J (H j.+1) k.
  apply/eqP=>hEqual.
  have hIndices:i=k.
    apply:val_inj; apply/eqP.
    rewrite -(@nth_uniq _ J
      (H j.+1:seq (compact_real_intervals R)) i k (ltn_ord i) (ltn_ord k) (fset_uniq _)).
    exact/eqP.
  by move:hDifferent; rewrite hIndices eqxx.
exact:(@subcritical_power_cantor_tree_point_gap R c m n s J H hc hm hmHalf hScales hJ hTree
  j _ _ (hMember i) (hMember k) hIntervals (v i) (v k) (hV i).2 (hV k).2).
Qed.

(** Source for [cantor_square_level_packing_exists]: supporting
    actual finite Euclidean packing for Federer 3.2.40,
    p. 276. Pair the true selected factor points. A
    differing coordinate and the actual nonexpanding projection
    prove separation in the original Euclidean metric. *)
Theorem cantor_square_level_packing_exists (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R) (J:compact_real_intervals R) (H:nat->{fset compact_real_intervals R})
    (A:set (real_line_metric R)) (j:nat):
  0<c ->0<m ->m<=1/2 ->is_rapid_power_cantor_scales c m n s ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  is_special_interval_tree_limit H A ->
  exists a:('I_(size (H j.+1:seq (compact_real_intervals R))) *
    'I_(size (H j.+1:seq (compact_real_intervals R))))%type ->
    inner_metric_space (@euclidean_inner_productP R 2),
    (forall i,euclidean_cantor_product A A (a i)) /\
    (forall i k,i!=k ->cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1<=mdist (a i) (a k)).
Proof.
move=>hc hm hmHalf hScales hJ hTree hA.
have hm1:m<1 by lra.
have [v hV]:=@power_cantor_level_point_selection_exists R c m J n H A j.+1 hc hm hm1 hTree hA.
pose I:=[the finType of ('I_(size (H j.+1:seq (compact_real_intervals R))) *
  'I_(size (H j.+1:seq (compact_real_intervals R))))%type].
pose a (i:I):=euclidean_real_plane_pair (v i.1) (v i.2).
have hPoint i:euclidean_cantor_product A A (a i).
  rewrite /euclidean_cantor_product /a /=
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  exact:conj (hV i.1).1 (hV i.2).1.
have hGap:=@cantor_level_selected_points_separated R c m n s J H A j v hc hm hmHalf hScales hJ hTree hV.
exists a; split; first exact hPoint.
move=>i k hDifferent.
case:(eqVneq i.1 k.1)=>[hFirstEqual|hFirstDifferent].
- have hSecondDifferent:i.2!=k.2.
    apply/eqP=>hSecondEqual.
    have hEqual:(i.1,i.2)=(k.1,k.2) by rewrite hFirstEqual hSecondEqual.
    rewrite -(surjective_pairing i) -(surjective_pairing k) in hEqual.
    by move:hDifferent; rewrite hEqual eqxx.
  have hProjection:=(metric_product_second_nonexpanding (@euclidean_real_plane_is_metric_product R)).2
    (a i) (a k) Logic.I Logic.I.
  rewrite mul1r /a !(metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) in hProjection.
  exact:le_trans (hGap _ _ hSecondDifferent) hProjection.
- have hProjection:=(metric_product_first_nonexpanding (@euclidean_real_plane_is_metric_product R)).2
    (a i) (a k) Logic.I Logic.I.
  rewrite mul1r /a !(metric_product_first_pair (@euclidean_real_plane_is_metric_product R)) in hProjection.
  exact:le_trans (hGap _ _ hFirstDifferent) hProjection.
Qed.
