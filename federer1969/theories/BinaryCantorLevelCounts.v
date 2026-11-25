(** Federer (1969), 3.3.20, pp. 306–308:
    actual original binary interval and square counts. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorLevelWidths PowerCantorUniformLevelWeights PowerCantorSplit RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_width_power_cost]: the
    actual common length at level j has m-power
    2^(-j), supporting the counts and original
    square hit measures in 3.3.20, pp. 306–308. *)
Lemma binary_cantor_width_power_cost (R:realType) (m:R):
  0<m ->forall j,real_power ((real_power 2 (-m^-1))^+j) m=((2:R)^-1)^+j.
Proof.
move=>hm.
have h2:(0<2:>R) by rewrite ltr0n.
have hLambda:0<real_power (2:R) (-m^-1):=real_power_strictly_positive _ h2.
have hCost:=@power_cantor_inverse_root_cost R 2 m h2 hm.
elim=>[|j ih];first by rewrite !expr0 real_power_one_base.
have hPow0:0<=(real_power (2:R) (-m^-1))^+j by apply:exprn_ge0;exact:ltW hLambda.
by rewrite !exprSr (@real_power_product R _ _ m hPow0 (ltW hLambda)) ih hCost.
Qed.

(** Source for [binary_cantor_level_count]: each actual
    original interval level has 2^j members. Actual
    conserved power weights and actual side lengths prove
    the count, supporting card(G_j)=4^j in
    3.3.20, pp. 306–308. No count is a
    defining family law or replacement-construction premise. *)
Theorem binary_cantor_level_count (R:realType) (c m:R)
    (J:compact_real_intervals R) H:
  0<c ->0<m ->m<1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c*real_power t m) J (fun _:nat=>2%N) H ->
  forall j,#|` H j|=(2^j)%N.
Proof.
move=>hc hm hm1 hJ hTree j.
have hWidth:=@binary_cantor_level_width R c m J H hc hm hJ hTree j.
have hBudget:=@power_cantor_uniform_level_weight_count R c m J (fun _:nat=>2%N) H j
  ((real_power 2 (-m^-1))^+j) hc hm hm1 hJ hTree hWidth.
rewrite (binary_cantor_width_power_cost hm) exprVn in hBudget.
have hPositive:(0<(2:R)^+j) by rewrite exprn_gt0 // ltr0n.
have hNonzero:(2:R)^+j!=0 by rewrite gt_eqF.
have hScalar:=congr1 (fun x:R=>x*(2:R)^+j) hBudget.
rewrite -mulrA mulVf // mulr1 mul1r in hScalar.
apply/eqP;by rewrite -(@eqr_nat R) natrX hScalar eqxx.
Qed.
