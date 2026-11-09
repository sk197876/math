(** Federer (1969), 3.3.20, p. 307: necessity of the original projection overlap inequalities. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP BinaryCantorSquareCover
  BinaryCantorOriginalFirstProjection BinaryCantorFullIntervalProjection BinaryCantorRatioBounds
  BinaryProjectedIntervalOverlap EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct EuclideanIntervalRectangles RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_first_projection_union_in_root]: each of the
    four original projected subintervals lies in the root projection,
    supporting the exact overlap locus in 3.3.20, p. 307. *)
Lemma binary_first_projection_union_in_root (R:realType) (s u v:R):
  0<=s ->s<=1 ->0<=u ->0<=v ->
  binary_projected_interval_union s u v `<=` (`[0,u+v]:set R).
Proof.
move=>hs hs1 hu hv z;rewrite /binary_projected_interval_union /= !in_itv /=.
move=>[[[/andP[h0 h1]|/andP[h0 h1]]|/andP[h0 h1]]|/andP[h0 h1]];
  apply/andP;split;nra.
Qed.

(** Source for [binary_original_projection_exact_overlap_locus]: for
    the unchanged original E, its projection fills the full root
    interval if and only if the two printed overlap inequalities hold,
    3.3.20, p. 307, in the ordered nonnegative quadrant. Necessity
    uses actual E containment in G_1; sufficiency uses the proved
    original compact-limit theorem. No deleted nullity claim is used. *)
Theorem binary_original_projection_exact_overlap_locus (R:realType) (c m u v:R)
    (J:compact_real_intervals R) H G (A:set (real_line_metric R)):
  0<c ->0<m ->m<1 ->0<u ->0<=v ->v<=u ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
    euclidean_cantor_product A A=(`[0,u+v]:set R) <->
    (1-2 * real_power 2 (-m^-1)) * u<=v /\
    (1-2 * real_power 2 (-m^-1)) * v<=real_power 2 (-m^-1) * u).
Proof.
move=>hc hm hm1 hu hv hvu hJ hTree hA hG;split.
- move=>hFull.
  have /andP[hs hsHalf]:=(binary_cantor_original_ratio_bounds hm hm1).1.
  apply:(@binary_projected_interval_overlap R _ u v hs hsHalf hu hv hvu).1.
  apply/seteqP;split=>z.
  + have hs1:real_power (2:R) (-m^-1)<=1 by lra.
    exact:(@binary_first_projection_union_in_root R (real_power 2 (-m^-1)) u v
      (ltW hs) hs1 (ltW hu) hv z).
  + move=>hz;rewrite -hFull in hz.
    have [x hx hValue]:=hz.
    have [D [hD hxD]]:=@binary_cantor_original_square_level_cover R H G A hA hG 1%N x hx.
    rewrite -(@binary_cantor_original_first_projection R c m u v J H G
      hc hm hm1 (ltW hu) hv hJ hTree hG).
    exists x=>//;by exists D.
- move=>[hMiddle hSide].
  exact:(@binary_original_cantor_square_full_interval_projection R c m u v J H G A
    hc hm hm1 hu hv hvu hJ hTree hA hG hMiddle hSide).
Qed.
