(** Federer (1969), 3.3.20, p. 307: the actual compact Borel partitions of E. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EqualCostIntervalTreeSpecial SpecialIntervalFamilyUP PowerConcaveIntervalGauge PowerCantorPairUP
  PowerCantorPair CantorSquareCompactMass BinaryCantorSquareLevelsUP BinaryCantorSquareCover
  BinaryCantorSquareLevelTopology EuclideanInnerProduct InnerMetric EuclideanCantorProduct
  EuclideanIntervalRectangles BorelPartition TopologicalBorel RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_square_piece_borel_partition]:
    the original family {T intersect E:T in G_j} is a Borel
    partition of the unchanged original E, 3.3.20, p. 307.
    Finite countability, actual compactness, original interval
    disjointness and the literal level cover prove all partition laws. *)
Theorem binary_original_square_piece_borel_partition (R:realType) (c m:R)
    (J:compact_real_intervals R) H G (A:set (real_line_metric R)) (f:R->R) j:
  0<c ->0<m ->m<1 ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  is_power_cantor_pair c m (fun _:nat=>2%N) A f ->
  is_borel_partition (euclidean_cantor_product A A)
    ((fun P:compact_real_intervals R*compact_real_intervals R=>
      euclidean_cantor_product A A `&` euclidean_interval_rectangle P.1 P.2) @` [set` G j]).
Proof.
move=>hc hm hm1 hTree hA hG hPair.
pose E:=euclidean_cantor_product A A.
pose piece (P:compact_real_intervals R*compact_real_intervals R):=
  E `&` euclidean_interval_rectangle P.1 P.2.
have hSpecial:=@equal_cost_interval_tree_special R _ (power_concave_interval_gauge hc hm hm1)
  J (fun _:nat=>2%N) H hTree.
have hFactor:=(@power_cantor_pair_properties R c m (fun _:nat=>2%N) A f hc hm hm1 hPair).1.
have hCompactE:compact E:=euclidean_cantor_product_compact hFactor hFactor.
constructor.
- apply:finite_set_countable;apply:finite_image;exact:finite_fset.
- move=>B C [P hP <-] [Q hQ <-] hDifferent.
  have hPQ:P!=Q by apply/eqP=>h;apply:hDifferent;by rewrite h.
  change (is_true (P \in G j)) in hP.
  change (is_true (Q \in G j)) in hQ.
  move:hP hQ;rewrite hG !in_fsetM=>/andP[hP0 hP1] /andP[hQ0 hQ1].
  apply/seteqP;split;last by move=>x [].
  move=>x [[_ [hxP0 hxP1]] [_ [hxQ0 hxQ1]]].
  case:(eqVneq P.1 Q.1)=>hFirst.
  + have hSecond:P.2!=Q.2.
      apply/eqP=>hSecond;have hEqual:P=Q by rewrite (surjective_pairing P) (surjective_pairing Q) hFirst hSecond.
      by rewrite hEqual eqxx in hPQ.
    have hDisjoint:=@special_tree_disjoint R _ H hSpecial j P.2 Q.2 hP1 hQ1 hSecond.
    have hx:(val P.2 `&` val Q.2) (EuclideanRealPlane.euclidean_real_plane_second x) by split.
    by rewrite hDisjoint in hx.
  + have hDisjoint:=@special_tree_disjoint R _ H hSpecial j P.1 Q.1 hP0 hQ0 hFirst.
    have hx:(val P.1 `&` val Q.1) (EuclideanRealPlane.euclidean_real_plane_first x) by split.
    by rewrite hDisjoint in hx.
- move=>B [P hP <-].
  have hClosed:=compact_closed (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)])
    (@original_interval_rectangle_compact R P.1 P.2).
  exact:closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)])
    (compact_closedI hCompactE hClosed)).
- apply/seteqP;split=>x.
  + by move=>[B [P hP <-] [hx _]].
  + move=>hx;have [P [hP hxP]]:=@binary_cantor_original_square_level_cover R H G A hA hG j x hx.
    exists (piece P);last by split.
    by exists P.
Qed.
