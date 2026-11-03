(** Federer (1969), 3.2.40, p. 276: actual
    real-valued finite level counts satisfy the original
    subdivision recurrence. Conserved weights prove it
    without assuming a cardinal formula for the tree. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge MetricDiameter
  RealPower RapidPowerCantorScalesUP RapidPowerCantorScalesLaws
  RapidPowerCantorTreeScales EqualCostIntervalTreeUP PowerCantorUniformLevelWeights
  CantorSplitRadiusUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rapid_power_cantor_level_count_recurrence]: supporting
    the actual packing-size estimate in Federer 3.2.40,
    p. 276. True interval counts satisfy N_(j+1)=n_j*N_j.
    The common positive power cost cancels from the two
    exact finite level sums and the original split law.
    No finite-family count is an extra hypothesis. *)
Lemma rapid_power_cantor_level_count_recurrence (R:realType) (c m:R)
    (n:nat->nat) (s:nat->R) (J:compact_real_intervals R) H:
  0<c ->0<m ->m<1 ->is_rapid_power_cantor_scales c m n s ->
  val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J n H ->forall j,
  (#|` H j.+1|%:R:R)=(n j)%:R*#|` H j|%:R.
Proof.
move=>hc hm hm1 hScales hJ hTree j.
have hWidth:=@rapid_power_cantor_tree_common_width R c m n s J H hc hm hm1 hScales hJ hTree.
have hOld:=@power_cantor_uniform_level_weight_count R c m J n H j (s j)
  hc hm hm1 hJ hTree (hWidth j).
have hNew:=@power_cantor_uniform_level_weight_count R c m J n H j.+1 (s j.+1)
  hc hm hm1 hJ hTree (hWidth j.+1).
have hCost:=cantor_split_radius_cost (rapid_power_cantor_split hScales j).
have hcNonzero:c!=0 by rewrite gt_eqF.
have hPowerCost:real_power (s j.+1) m=real_power (s j) m/(n j)%:R.
  apply:(mulfI hcNonzero).
  by rewrite hCost mulrA.
have hj2:(2<=j.+2)%N by [].
have hCountBound:(2<=n j)%N:=leq_trans hj2 (rapid_power_cantor_count hScales j).
have hnPositive:(0<((n j)%:R:R)) by rewrite ltr0n; exact:leq_trans (leqnSn 1) hCountBound.
rewrite hPowerCost in hNew.
have hMultiplied:=congr1 (fun z:R=>z*(n j)%:R) hNew.
have hAlgebra:((#|` H j.+1|%:R:R)*(real_power (s j) m/(n j)%:R))*(n j)%:R=
    #|` H j.+1|%:R*real_power (s j) m by field; rewrite (gt_eqF hnPositive).
rewrite hAlgebra mul1r in hMultiplied.
have hWidthPositive:=rapid_power_cantor_width_positive hScales j.
have hPowerPositive:=@real_power_strictly_positive R (s j) m hWidthPositive.
have hPowerNonzero:real_power (s j) m!=0 by rewrite gt_eqF.
apply:(mulIf hPowerNonzero).
by rewrite hMultiplied -mulrA hOld mulr1.
Qed.
