(** Federer (1969), 3.3.20, pp. 308–309: corrected positive-diameter finite-stage attainment. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP EuclideanInnerProduct InnerMetric
  EuclideanIntervalRectangles CriticalSingleHitDescent FiniteFamilyNoTwo
  FiniteCellHitMeasureUP FiniteCellHitIndicesLaws CriticalSquareHitMeasureUP
  MetricDiameter RecurrentContraction RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_positive_diameter_attainment]:
    the finite-stage comparison in 3.3.20, pp. 308–309, with its
    necessary positive-diameter qualification. If attainment failed,
    the proved original-square similarity and Omega argument would force
    every actual hit family to be a singleton. Their literal costs
    tend to zero, contradicting the positive bound d. The separate
    actual singleton counterexample explains why d=0 is not asserted. *)
Theorem critical_original_positive_diameter_attainment (R:realType) (c d:R)
    (J:compact_real_intervals R) H G psi (A:set (real_line_metric R))
    (V:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->0<d ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  is_critical_square_hit_measures G psi ->(extended_metric_diameter V<=d%:E)%E ->
  exists k,(psi k V<=d%:E)%E.
Proof.
move=>hc hd hJ hTree hA hG hPsi hDiameter;apply:contrapT=>hNo.
pose hits k:=finite_cell_hit_indices (G k) (fun S=>euclidean_interval_rectangle S.1 S.2) V.
have hNonempty k:hits k!=fset0.
  apply/negP=>/eqP hEmpty;apply:hNo;exists k.
  rewrite /hits in hEmpty.
  rewrite hPsi hEmpty cardfs0 mul0r lee_fin;exact:ltW hd.
have hSingles:forall j,exists P,hits j=[fset P].
  elim=>[|j [P hP]].
  - apply:finite_family_no_two_singleton (hNonempty 0%N) _.
    have hOnly P:P \in hits 0%N ->P=(J,J).
      move=>/finite_cell_hit_indices_membership[hP _].
      move:hP;rewrite hG (equal_cost_tree_root hTree) in_fsetM !in_fset1=>/andP[/eqP hFirst /eqP hSecond].
      case:P hFirst hSecond=>S T /= -> ->;by [].
    move=>[P [Q [hP [hQ hDifferent]]]].
    move:hDifferent;by rewrite (hOnly P hP) (hOnly Q hQ) eqxx.
  - exact:(@critical_original_single_hit_descent R c d J H G psi A V j P
      hc (ltW hd) hJ hTree hA hG hPsi hDiameter hNo hP).
have hQuarter:0<(1/4:R)<1 by apply/andP;split;lra.
have [j hj]:=geometric_contraction_small hQuarter (sqrtr_ge0 (2:R)) hd.
have [P hP]:=hSingles j.
rewrite /hits in hP.
apply:hNo;exists j;rewrite hPsi hP cardfs1 mul1r lee_fin.
have hCost:(Num.sqrt (2:R)/(4:R)^+j)=(1/4:R)^+j*Num.sqrt 2
  by rewrite mul1r exprVn mulrC.
rewrite hCost;exact:ltW hj.
Qed.
