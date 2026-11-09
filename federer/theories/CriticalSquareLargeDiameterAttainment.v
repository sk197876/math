(** Federer (1969), 3.3.20, pp. 308–309:
    the actual four-certificate contradiction after the half-sigma reduction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EuclideanInnerProduct InnerMetric EuclideanIntervalRectangles BinaryCantorSquareLevelsUP
  BinaryCantorSquareCount CriticalSquareHitMeasureUP FiniteCellHitMeasureUP
  FiniteCellMissingCount CriticalCornerFourCertificates CriticalSquareMissingScalarContradiction
  MetricDiameter RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_square_large_diameter_attainment]:
    the exact four successive squeezes in 3.3.20,
    pp. 308–309, for the original G_j,
    psi_j and arbitrary original S once its
    actual diameter is at least sqrt(2)/2.
    All missing-count bounds and geometric certificates
    are derived. The earlier similarity/base-case
    reduction is a separate supporting argument. *)
Theorem critical_square_large_diameter_attainment (R:realType) (c d:R)
    (J:compact_real_intervals R) H G psi
    (T:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->is_critical_square_hit_measures G psi ->
  (extended_metric_diameter T<=d%:E)%E ->Num.sqrt (2:R)/2<=d ->
  exists j,(psi j T<=d%:E)%E.
Proof.
move=>hc hJ hTree hG hPsi hDiameter hHalf.
apply:contrapT=>hNo.
pose hits j:=finite_cell_hit_indices (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) T.
pose missed j:=#|` ((G j `\` hits j)%fset)|.
pose sigma:=1-d/Num.sqrt (2:R).
have hRoot:0<Num.sqrt (2:R) by rewrite sqrtr_gt0 ltr0n.
have hRootNZ:Num.sqrt (2:R)!=0 by rewrite gt_eqF.
have hSigma:sigma*Num.sqrt (2:R)=Num.sqrt (2:R)-d by rewrite /sigma;field;by rewrite hRootNZ.
have hPower j:0<(4:R)^+j by rewrite exprn_gt0 // ltr0n.
have hCard j:#|` G j|=(4^j)%N.
  have hm:0<(1/2:R) by lra.
  have hm1:(1/2:R)<1 by lra.
  exact:(@binary_cantor_original_square_count R c (1/2:R) J H G hc hm hm1 hJ hTree hG j).
have hTotal j:(missed j)%:R+(#|` hits j|%:R:R)=(4:R)^+j.
  have h:=congr1 (fun n:nat=>(n%:R:R))
    (@finite_cell_missing_count_identity _ _ (G j) (fun P=>euclidean_interval_rectangle P.1 P.2) T).
  by rewrite natrD (hCard j) natrX in h.
have hStrict j:d<(#|` hits j|%:R:R)*(Num.sqrt (2:R)/(4:R)^+j).
  have h:(d%:E<psi j T)%E.
    rewrite ltNge;apply/negP=>hBound;apply:hNo;by exists j.
  by rewrite hPsi lte_fin in h.
have hMissing j:(missed j)%:R<(4:R)^+j*sigma.
  have h:=hStrict j.
  have hStrictMult:d*(4:R)^+j<(#|` hits j|%:R:R)*Num.sqrt (2:R).
    have hh:=h.
    rewrite -(ltr_pM2r (hPower j)) in hh.
    by rewrite mulrA divfK ?gt_eqF // in hh.
  have hTotalScaled:=congr1 (fun t:R=>t*Num.sqrt (2:R)) (hTotal j).
  have hSigmaScaled:=congr1 (fun t:R=>t*(4:R)^+j) hSigma.
  nra.
have hSigmaPositive:0<sigma.
  have h:=hMissing 0%N.
  rewrite expr0 mul1r in h.
  have hNonnegative:0<=((missed 0%N)%:R:R) by exact:ler0n.
  lra.
have hSigmaHalf:sigma<=1/2 by nra.
have [h8 [h20 [h14 h10]]]:=@critical_corner_four_actual_certificates R c J H G T hc hJ hTree hG.
have hConvert (v:R):
    ((Num.sqrt (2:R)*(1-v))%:E<=extended_metric_diameter T)%E ->sigma<=v.
  move=>hBound.
  have h:=le_trans hBound hDiameter.
  rewrite lee_fin in h;nra.
apply:(@critical_square_missing_scalar_contradiction R sigma missed hSigmaPositive hSigmaHalf).
- move=>j _;exact:hMissing j.
- move=>j hj hj8;apply:hConvert;exact:h8 j hj hj8.
- move=>j hj hj20;apply:hConvert;exact:h20 j hj hj20.
- move=>j hj hj14;apply:hConvert;exact:h14 j hj hj14.
- move=>j hj hj10;apply:hConvert;exact:h10 j hj hj10.
Qed.
