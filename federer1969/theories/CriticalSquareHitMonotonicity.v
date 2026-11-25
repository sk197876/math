(** Federer (1969), 3.3.20, p. 308: the actual finite-stage hit measures decrease. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  BinaryCantorSquareLevelsUP BinarySquareHitRefinementCount CriticalSquareHitMeasureUP
  FiniteCellHitMeasureUP EuclideanInnerProduct InnerMetric EuclideanIntervalRectangles RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_square_hit_measures_decrease]:
    psi_j(S)>=psi_(j+1)(S) for every original arbitrary S,
    3.3.20, p. 308. The proved original four-child hit bound and
    literal reciprocal-four weights give the result; no monotonicity
    or count law is assumed in the independent measure specification. *)
Theorem critical_original_square_hit_measures_decrease (R:realType) (c:R)
    (J:compact_real_intervals R) H G psi:
  0<c ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->is_critical_square_hit_measures G psi ->
  forall j V,(psi j.+1 V<=psi j V)%E.
Proof.
move=>hc hTree hG hPsi j V.
have hm:0<(1/2:R) by lra.
have hm1:(1/2:R)<1 by lra.
have hCount:=@binary_original_square_hit_refinement_count R c (1/2:R) J H G j V
  hc hm hm1 hTree hG.
pose a:=#|` finite_cell_hit_indices (G j.+1) (fun P=>euclidean_interval_rectangle P.1 P.2) V|.
pose b:=#|` finite_cell_hit_indices (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) V|.
have hReal:(a%:R<=4 * b%:R:>R) by rewrite -natrM ler_nat.
have hPositive:0<(4:R)^+j by rewrite exprn_gt0 // ltr0n.
have hWeight:0<=Num.sqrt (2:R)/(4:R)^+j.+1 by apply:divr_ge0;[exact:sqrtr_ge0|by rewrite exprn_ge0 // ler0n].
have hScaled:=ler_wpM2l hWeight hReal.
have hWeightIdentity:Num.sqrt (2:R)/(4:R)^+j.+1 * 4=Num.sqrt (2:R)/(4:R)^+j.
  rewrite exprS;field;by rewrite ?gt_eqF // ?pnatr_eq0.
rewrite (hPsi j.+1) (hPsi j) lee_fin.
change (is_true (a%:R * (Num.sqrt (2:R)/(4:R)^+j.+1)<=b%:R * (Num.sqrt (2:R)/(4:R)^+j))).
rewrite [a%:R * _]mulrC [b%:R * _]mulrC.
by rewrite mulrA hWeightIdentity in hScaled.
Qed.
