(** Federer (1969), 3.3.20, pp. 308–309:
    actual original corner pairs give the printed missing-count bounds. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EuclideanInnerProduct InnerMetric EuclideanIntervalRectangles BinaryCantorSquareLevelsUP
  CriticalCornerIntervalSelection CriticalCornerPairingPatternsUP CriticalCornerSquarePairs
  FinitePairedMetricDiameter FiniteCellHitMeasureUP MetricDiameter RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_corner_original_missing_bound]:
    the four Omega certificates of 3.3.20,
    pp. 308–309, as actual original-square
    diameter inequalities. A proved finite pattern,
    its actual corner placement and a small actual
    missing count suffice. No square-separation or
    diameter premise is added to the theorem. *)
Theorem critical_corner_original_missing_bound (R:realType) (c:R)
    (J:compact_real_intervals R) H G j n budget L
    (T:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->(2<=j)%N ->
  is_critical_corner_pairing_pattern n budget L ->
  (forall p,p \in L ->(4*(p.1+1)<=4^j)%N /\(4*(p.2+1)<=4^j)%N) ->
  (#|` ((G j `\` finite_cell_hit_indices (G j)
    (fun P=>euclidean_interval_rectangle P.1 P.2) T)%fset)|<2*n)%N ->
  ((Num.sqrt (2:R) * (1-(budget+4)%:R/(2*(4:R)^+j)))%:E<=extended_metric_diameter T)%E.
Proof.
move=>hc hJ hTree hG hj hPattern hSize hCount.
pose r:=(4:R)^+j.
have hr:0<r by rewrite /r exprn_gt0 // ltr0n.
have [C hC]:=@critical_corner_original_interval_selection_exists R c J H j hc hJ hTree hj.
have hSizeR p:p \in L ->((p.1+1)%:R:R)/r<=1/4 /\((p.2+1)%:R:R)/r<=1/4.
  move=>hp;have [h0 h1]:=hSize p hp.
  have hR0:((4*(p.1+1))%:R:R)<=(4^j)%:R by rewrite ler_nat.
  have hR1:((4*(p.2+1))%:R:R)<=(4^j)%:R by rewrite ler_nat.
  rewrite natrM natrX -/r in hR0 hR1.
  split;rewrite ler_pdivrMr //;lra.
have [e [hInjective [hEndpoints hDistance]]]:=@critical_corner_actual_square_pairs R r
  (H j) (G j) C n budget L hr (hG j) hC hPattern hSizeR.
pose I:=[the finType of (bool*'I_(size L))%type].
have hK:{subset (fset0:{fset (compact_real_intervals R*compact_real_intervals R)})<=
    ((G j `\` finite_cell_hit_indices (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) T)%fset)}.
  by move=>P;rewrite in_fset0.
have hEnd i t:e (i,t) \in G j /\e (i,t) \notin fset0.
  split;first exact:hEndpoints;by rewrite in_fset0.
apply:(@finite_paired_missing_metric_diameter R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)] _ I
  (G j) fset0 (fun P=>euclidean_interval_rectangle P.1 P.2) T e
  (Num.sqrt 2*(1-(budget+4)%:R/(2*r))) hK hInjective hEnd hDistance).
by rewrite cardfs0 add0n /I card_prod card_bool card_ord hPattern.1.
Qed.
