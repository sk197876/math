(** Federer (1969), 3.3.20, pp. 308–309:
    all four printed actual opposite-corner missing-count certificates. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EuclideanInnerProduct InnerMetric EuclideanIntervalRectangles BinaryCantorSquareLevelsUP
  CriticalCornerPairingPatternsUP CriticalCornerPairingPatterns CriticalCornerMissingBound
  FiniteCellHitMeasureUP MetricDiameter RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_corner_pattern_offset_cap]: supporting
    actual finite corner placements for 3.3.20,
    pp. 308–309. Every admissible two-digit
    original offset is at most fifteen. *)
Lemma critical_corner_pattern_offset_cap n budget L:
  is_critical_corner_pairing_pattern n budget L ->
  forall p,p \in L ->(p.1<=15)%N /\(p.2<=15)%N.
Proof.
move=>hPattern p hp.
have hSmall a:a \in [::0;3;12;15] ->(a<=15)%N.
  rewrite !inE=>/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];by [].
have /andP[hFirst hSecond]:=allP hPattern.2.2.1 _ hp.
by split;apply:hSmall.
Qed.

(** Source for [critical_corner_four_actual_certificates]:
    the original 8,20,14,10-pair implications
    of 3.3.20, pp. 308–309, with
    distances sqrt(2) times respectively 1-5/4^j,
    1-14/4^j, 1-(19/2)/4^j and 1-8/4^j.
    Every finite pattern is placed in the ACTUAL
    original G_j family and its distinctness and
    separation are proved. No geometric certificate
    is an additional premise. *)
Theorem critical_corner_four_actual_certificates (R:realType) (c:R)
    (J:compact_real_intervals R) H G
    (T:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->
  let missed j:=#|` ((G j `\` finite_cell_hit_indices (G j)
    (fun P=>euclidean_interval_rectangle P.1 P.2) T)%fset)| in
  (forall j,(2<=j)%N ->(missed j<8)%N ->
    ((Num.sqrt (2:R)*(1-5/(4:R)^+j))%:E<=extended_metric_diameter T)%E) /\
  (forall j,(3<=j)%N ->(missed j<20)%N ->
    ((Num.sqrt (2:R)*(1-14/(4:R)^+j))%:E<=extended_metric_diameter T)%E) /\
  (forall j,(3<=j)%N ->(missed j<14)%N ->
    ((Num.sqrt (2:R)*(1-(19/2)/(4:R)^+j))%:E<=extended_metric_diameter T)%E) /\
  (forall j,(3<=j)%N ->(missed j<10)%N ->
    ((Num.sqrt (2:R)*(1-8/(4:R)^+j))%:E<=extended_metric_diameter T)%E).
Proof.
move=>hc hJ hTree hG missed.
have hNonzero j:(4:R)^+j!=0.
  have hPositive:0<(4:R)^+j by rewrite exprn_gt0 // ltr0n.
  by rewrite gt_eqF.
have hBound j n budget L:
    (2<=j)%N ->is_critical_corner_pairing_pattern n budget L ->
    (forall p,p \in L ->(4*(p.1+1)<=4^j)%N /\(4*(p.2+1)<=4^j)%N) ->
    (missed j<2*n)%N ->
    ((Num.sqrt (2:R)*(1-(budget+4)%:R/(2*(4:R)^+j)))%:E<=extended_metric_diameter T)%E.
  exact:(@critical_corner_original_missing_bound R c J H G j n budget L T hc hJ hTree hG).
have hSize j (L:seq (nat*nat)):(3<=j)%N ->
    (forall p,p \in L ->(p.1<=15)%N /\(p.2<=15)%N) ->
    forall p,p \in L ->(4*(p.1+1)<=4^j)%N /\(4*(p.2+1)<=4^j)%N.
  move=>hj hCap p hp;have [h1 h2]:=hCap p hp.
  have hPower:(64<=4^j)%N:=@leq_pexp2l 4 3 j (erefl true) hj.
  have hLeft:(4*(p.1+1)<=64)%N:=leq_mul (leqnn 4) (leq_add h1 (leqnn 1)).
  have hRight:(4*(p.2+1)<=64)%N:=leq_mul (leqnn 4) (leq_add h2 (leqnn 1)).
  split;[exact:leq_trans hLeft hPower|exact:leq_trans hRight hPower].
split.
- move=>j hj hMiss.
  have [L [hPattern hCap]]:=critical_corner_four_offsets_exist.
  have hSmall p:p \in L ->(4*(p.1+1)<=4^j)%N /\(4*(p.2+1)<=4^j)%N.
    move=>hp;have /andP[h1 h2]:=allP hCap _ hp.
    have hPower:(16<=4^j)%N:=@leq_pexp2l 4 2 j (erefl true) hj.
    have hLeft:(4*(p.1+1)<=16)%N:=leq_mul (leqnn 4) (leq_add h1 (leqnn 1)).
    have hRight:(4*(p.2+1)<=16)%N:=leq_mul (leqnn 4) (leq_add h2 (leqnn 1)).
    split;[exact:leq_trans hLeft hPower|exact:leq_trans hRight hPower].
  have h:=hBound j 4 6 L hj hPattern hSmall hMiss.
  have hEq:((6+4)%N)%:R/(2*(4:R)^+j)= 5/(4:R)^+j by field;rewrite hNonzero.
  by rewrite hEq in h.
split.
- move=>j hj hMiss.
  have [L hPattern]:=critical_corner_ten_offsets_exist.
  have hj2:(2<=j)%N:=leq_trans (erefl true:(2<=3)%N) hj.
  have h:=hBound j 10 24 L hj2 hPattern (hSize j L hj (critical_corner_pattern_offset_cap hPattern)) hMiss.
  have hEq:((24+4)%N)%:R/(2*(4:R)^+j)= 14/(4:R)^+j by field;rewrite hNonzero.
  by rewrite hEq in h.
split.
- move=>j hj hMiss.
  have [L hPattern]:=critical_corner_seven_offsets_exist.
  have hj2:(2<=j)%N:=leq_trans (erefl true:(2<=3)%N) hj.
  have h:=hBound j 7 15 L hj2 hPattern (hSize j L hj (critical_corner_pattern_offset_cap hPattern)) hMiss.
  have hEq:((15+4)%N)%:R/(2*(4:R)^+j)=(19/2)/(4:R)^+j by field;rewrite hNonzero.
  by rewrite hEq in h.
- move=>j hj hMiss.
  have [L hPattern]:=critical_corner_five_offsets_exist.
  have hj2:(2<=j)%N:=leq_trans (erefl true:(2<=3)%N) hj.
  have h:=hBound j 5 12 L hj2 hPattern (hSize j L hj (critical_corner_pattern_offset_cap hPattern)) hMiss.
  have hEq:((12+4)%N)%:R/(2*(4:R)^+j)= 8/(4:R)^+j by field;rewrite hNonzero.
  by rewrite hEq in h.
Qed.
