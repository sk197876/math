(** Federer (1969), 3.2.40, p. 276: the actual
    separated finite level points give arbitrarily large
    tube quotients for the proved rapid schedule. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology ring lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge RealPower
  EuclideanInnerProduct InnerMetric EuclideanCantorProduct EuclideanBallVolume
  RapidPowerCantorScalesUP RapidPowerCantorScalesLaws RapidPowerCantorTreeScales
  RapidPowerCantorLevelCounts PowerCantorUniformLevelWeights
  EqualCostIntervalTreeUP SpecialIntervalFamilyUP CantorSplitRadius
  CantorSquareLevelPacking SeparatedPlanarTubeLower MinkowskiContents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rapid_cantor_square_step_tube_lower_bound]: supporting
    infinite upper content in Federer 3.2.40, p. 276.
    At the true gap/4, indexed actual source points give a
    quotient at least alpha(2)*(j+1)/8. The finite level count,
    split cost, gap lower bound and rapid scalar growth are
    all proved consequences of the independent original laws. *)
Lemma rapid_cantor_square_step_tube_lower_bound (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R) (J:compact_real_intervals R)
    (H:nat->{fset compact_real_intervals R}) (A:set (real_line_metric R)):
  0<c ->0<m ->m<=1/2 ->is_rapid_power_cantor_scales c m n s ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->
  is_special_interval_tree_limit H A ->forall j,
    ((euclidean_unit_ball_volume R 2/8*j.+1%:R)%:E<=
      minkowski_tube_quotient 1 (euclidean_cantor_product A A)
        ((cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1)/4))%E.
Proof.
move=>hc hm hmHalf hScales hJ hTree hA j.
have hm1:m<1 by lra.
pose N:=size (H j:seq (compact_real_intervals R)).
pose M:=size (H j.+1:seq (compact_real_intervals R)).
pose I:=[the finType of ('I_M*'I_M)%type].
pose g:=cantor_split_spacing (s j) (n j) (s j.+1)-s j.+1.
have hGap:=@rapid_power_cantor_gap_bounds R c m n s hc hm hmHalf hScales j.
have hg:0<g:=hGap.2.1.
have [a [hInside hSeparated]]:=@cantor_square_level_packing_exists R c m n s J H A j
  hc hm hmHalf hScales hJ hTree hA.
have hPacking:=@separated_indexed_planar_tube_lower_bound R I (euclidean_cantor_product A A)
  a g hg hInside hSeparated.
have hCard:(#|I|=M*M)%N by rewrite /I card_prod !card_ord.
rewrite hCard natrM in hPacking.
have hCount:(M%:R:R)=(n j)%:R*N%:R:=
  @rapid_power_cantor_level_count_recurrence R c m n s J H hc hm hm1 hScales hJ hTree j.
have hWidth:=@rapid_power_cantor_tree_common_width R c m n s J H hc hm hm1 hScales hJ hTree.
have hWeight:=@power_cantor_uniform_level_weight_count R c m J n H j (s j)
  hc hm hm1 hJ hTree (hWidth j).
have hScaledCount:(N%:R)^+2*s j=real_power (s j) (1-2 * m).
  exact:(@power_cantor_square_scaled_count R m (s j) N
    (rapid_power_cantor_width_positive hScales j) hWeight).
have hj2:(2<=j.+2)%N by [].
have hNBound:(2<=n j)%N:=leq_trans hj2 (rapid_power_cantor_count hScales j).
have hnPositive:(0<((n j)%:R:R)) by rewrite ltr0n; exact:leq_trans (leqnSn 1) hNBound.
have hMultiplier:(0<=(M%:R:R)^+2):=exprn_ge0 2 (ler0n R M).
have hGapScaled:=ler_wpM2l hMultiplier hGap.1.
have hAlgebra:(((n j)%:R*N%:R)^+2*(s j/(n j)%:R):R)=
    (n j)%:R*((N%:R)^+2*s j) by field; rewrite (gt_eqF hnPositive).
rewrite hCount hAlgebra hScaledCount -hCount in hGapScaled.
have hGrowth:=rapid_power_cantor_growth hScales j.
have hSize:j.+1%:R<=(M%:R)^+2*g:=le_trans hGrowth hGapScaled.
have hCoefficient:0<=euclidean_unit_ball_volume R 2/8.
  apply:divr_ge0; first exact:ltW (euclidean_unit_ball_volumeE R 2).2.
  exact:ler0n.
have hLower:=ler_wpM2l hCoefficient hSize.
have hCoefficientAlgebra:(euclidean_unit_ball_volume R 2/8)*((M%:R)^+2*g)=
    (M%:R*M%:R*euclidean_unit_ball_volume R 2*g/8) by ring.
rewrite hCoefficientAlgebra in hLower.
apply:le_trans _ hPacking; by rewrite lee_fin.
Qed.
