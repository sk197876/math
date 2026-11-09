(** Federer (1969), 3.3.20, p. 308: actual initial first-split reduction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EuclideanInnerProduct InnerMetric EuclideanIntervalRectangles BinaryCantorSquareLevelsUP
  CriticalSquareHitMeasureUP FiniteCellHitMeasureUP FiniteCellHitIndicesLaws
  CriticalFirstLevelSquares CriticalFirstLevelSquareGeometry CriticalSecondLevelSquares
  CriticalSecondLevelMissingCertificates CriticalSecondLevelVerticalCertificates
  CriticalSquareStrictMissingCount CriticalAdjacentBaseScalar FourCornerHitAlternative
  MetricDiameter MetricDiameterUP RealPower CriticalFirstLevelIntervalSelection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_first_split_diameter_reduction]:
    the initial Omega argument in 3.3.20, p. 308. If two original
    first-level squares are hit, failure of finite-stage attainment
    forces diameter at least sqrt(2)/2. Both rows and columns, actual
    descendants, strict missing counts and all endpoint gaps are proved. *)
Theorem critical_original_first_split_diameter_reduction (R:realType) (c d:R)
    (J:compact_real_intervals R) H G psi
    (T:set (inner_metric_space (@euclidean_inner_productP R 2))):
  0<c ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c  *  real_power t (1/2:R)) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->is_critical_square_hit_measures G psi ->
  (extended_metric_diameter T<=d%:E)%E ->
  (exists P Q,P \in finite_cell_hit_indices (G 1%N)
      (fun S=>euclidean_interval_rectangle S.1 S.2) T /\
    Q \in finite_cell_hit_indices (G 1%N)
      (fun S=>euclidean_interval_rectangle S.1 S.2) T /\P!=Q) ->
  ~ (exists j,(psi j T<=d%:E)%E) ->Num.sqrt (2:R)/2<=d.
Proof.
move=>hc hJ hTree hG hPsi hDiameter [P [S [hP [hS hDifferent]]]] hNo.
have [Q [hQ [hQMember [hQExhaust hQCoord]]]]:=
  @critical_first_level_original_squares R c J H G hc hJ hTree hG.
have [hPM [x [hxP hxT]]]:=proj1 (finite_cell_hit_indices_membership _ _ _ _) hP.
have [hSM [y [hyS hyT]]]:=proj1 (finite_cell_hit_indices_membership _ _ _ _) hS.
have [[b e] hPE]:=hQExhaust P hPM.
have [[f g] hSE]:=hQExhaust S hSM.
have hBitDifferent:(b,e)!=(f,g).
  apply/negP=>/eqP hEqual;move:hDifferent;by rewrite hPE hSE hEqual eqxx.
have hDistance p q:T p ->T q ->mdist p q<=d.
  move=>hp hq.
  have h:=le_trans (metric_diameter_upper (extended_metric_diameter_specification T) hp hq) hDiameter.
  by rewrite lee_fin in h.
have hHalf:(1/2:R)<=d.
  move:hxP hyS;rewrite hPE hSE;move=>[hx0 hx1] [hy0 hy1].
  rewrite (hQCoord (b,e)).1 in hx0;rewrite (hQCoord (b,e)).2 in hx1.
  rewrite (hQCoord (f,g)).1 in hy0;rewrite (hQCoord (f,g)).2 in hy1.
  exact:le_trans (@critical_first_level_distinct_square_gap R b e f g x y
    hBitDifferent hx0 hx1 hy0 hy1) (hDistance _ _ hxT hyT).
pose hit k:=(Q k \in finite_cell_hit_indices (G 1%N)
  (fun S=>euclidean_interval_rectangle S.1 S.2) T).
have [hDiagonal|[axis [b0 hRow]]]:=four_corner_hit_alternative hit.
- have [a [b0 [hA hB]]]:=hDiagonal.
  have [_ [p [[hp0 hp1] hpT]]]:=proj1 (finite_cell_hit_indices_membership _ _ _ _) hA.
  have [_ [q [[hq0 hq1] hqT]]]:=proj1 (finite_cell_hit_indices_membership _ _ _ _) hB.
  rewrite (hQCoord (a,b0)).1 in hp0;rewrite (hQCoord (a,b0)).2 in hp1.
  rewrite (hQCoord (negb a,negb b0)).1 in hq0;rewrite (hQCoord (negb a,negb b0)).2 in hq1.
  exact:le_trans (@critical_first_level_diagonal_square_gap R a b0 p q hp0 hp1 hq0 hq1)
    (hDistance _ _ hpT hqT).
- have [D [hD [hDMember hDCoord]]]:=
    @critical_second_level_original_squares R c J H G hc hJ hTree hG.
  have hParent p t u z:
      euclidean_interval_rectangle (D (p,(t,u))).1 (D (p,(t,u))).2 z ->
      euclidean_interval_rectangle (Q p).1 (Q p).2 z.
    move=>[hz0 hz1].
    rewrite (hDCoord (p,(t,u))).1 in hz0;rewrite (hDCoord (p,(t,u))).2 in hz1.
    split.
    - rewrite (hQCoord p).1;exact:(@critical_second_level_interval_in_parent R p.1 t _ hz0).
    - rewrite (hQCoord p).2;exact:(@critical_second_level_interval_in_parent R p.2 u _ hz1).
  have hNotFlip:forall t:bool,negb t=t ->False by move=>[] /=;discriminate.
  have hStrict:=@critical_original_strict_missing_counts R c d J H G psi T hc hJ hTree hG hPsi hNo 2%N.
  have hSixteen:(4:R)^+2= 16 by ring.
  rewrite hSixteen in hStrict.
  pose r:=#|` ((G 2%N `\` finite_cell_hit_indices (G 2%N)
    (fun S=>euclidean_interval_rectangle S.1 S.2) T)%fset)|.
  change (is_true ((r%:R:R)<16 * (1-d/Num.sqrt (2:R)))) in hStrict.
  have hCertificates:
      ((r<12)%N ->((11/16:R)%:E<=extended_metric_diameter T)%E) /\
      ((r<9)%N ->((7/8:R)%:E<=extended_metric_diameter T)%E).
    case:axis hRow=>hRow.
    - apply:(@critical_second_level_vertical_missing_certificates R (G 2%N) D b0 T hD hDMember).
      + move=>k;exact:(hDCoord k).2.
      + move=>[p [t u]] z hz hT.
        have hParentHit:hit (negb b0,p).
          apply/finite_cell_hit_indices_membership;split;first exact:hQMember.
          exists z;split=>//;exact:hParent _ _ _ _ hz.
        have hEqual:=hRow _ hParentHit;exact:hNotFlip b0 hEqual.
    - apply:(@critical_second_level_adjacent_missing_certificates R (G 2%N) D b0 T hD hDMember).
      + move=>k;exact:(hDCoord k).1.
      + move=>[p [t u]] z hz hT.
        have hParentHit:hit (p,negb b0).
          apply/finite_cell_hit_indices_membership;split;first exact:hQMember.
          exists z;split=>//;exact:hParent _ _ _ _ hz.
        have hEqual:=hRow _ hParentHit;exact:hNotFlip b0 hEqual.
  apply:(critical_adjacent_base_scalar_bridge hHalf hStrict).
  + move=>hr;have h:=le_trans (hCertificates.1 hr) hDiameter;by rewrite lee_fin in h.
  + move=>hr;have h:=le_trans (hCertificates.2 hr) hDiameter;by rewrite lee_fin in h.
Qed.
