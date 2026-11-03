(** Federer (1969), 3.2.40, p. 276: actual
    finite-level square covers control the tube quotient
    at the common interval width. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric RealMetricBackground
  EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles
  CompactIntervalGauge EqualCostIntervalTreeUP SpecialIntervalFamilyUP
  PowerCantorUniformLevelWeights RealPower MinkowskiContents EuclideanBallVolume
  FinitePlanarScaledTubeCover MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [power_cantor_square_level_tube_bound]: supporting
    the finite and zero lower contents in Federer 3.2.40,
    p. 276. Actual pairs of level intervals cover the original
    same-factor Cantor square. Their diameter bounds, the
    actual planar ball volume and conserved power weights give
    a bound by a fixed constant times s^(1-2m). No rapid
    growth, rectifiability or content identity is assumed. *)
Lemma power_cantor_square_level_tube_bound (R:realType) (c m:R)
    (J:compact_real_intervals R) (n:nat->nat)
    (H:nat->{fset compact_real_intervals R}) (A:set (real_line_metric R)) j (s:R):
  (0<c)%R ->(0<m)%R ->(m<1)%R ->val J=(`[0%R,1%R]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>(c*real_power t m)%R) J n H ->
  is_special_interval_tree_limit H A ->(0<s)%R ->
  (forall S,S \in H j ->fine (@extended_metric_diameter R
    [the metricType R of real_line_metric R] (val S))=s) ->
  minkowski_tube_quotient 1 (euclidean_cantor_product A A) s<=
    ((euclidean_unit_ball_volume R 2*(Num.sqrt 2+1)^+2/2)*real_power s (1-2 * m))%R%:E.
Proof.
move=>hc hm hm1 hJ hTree hA hs hWidth.
pose E:=inner_metric_space (@euclidean_inner_productP R 2).
pose W:=euclidean_cantor_product A A.
pose N:=size (H j:seq (compact_real_intervals R)).
pose I:=[the finType of ('I_N*'I_N)%type].
pose U (i:'I_N):=nth J (H j) i.
pose Q (i:I):=euclidean_interval_rectangle (U i.1) (U i.2).
have hMember (i:'I_N):U i \in H j:=mem_nth J (ltn_ord i).
have hCover:W `<=` \bigcup_i Q i.
  move=>x [hx hy].
  have [S [hS hxS]]:=(hA (euclidean_real_plane_first x)).1 hx j.
  have [T [hT hyT]]:=(hA (euclidean_real_plane_second x)).1 hy j.
  have hi:(index S (H j)<N)%N by rewrite /N index_mem.
  have hk:(index T (H j)<N)%N by rewrite /N index_mem.
  exists ((Ordinal hi,Ordinal hk):I); first exact Logic.I.
  by rewrite /Q /U /= !nth_index.
have hDiameter (i:I):extended_metric_diameter (Q i)<=(Num.sqrt 2*s)%R%:E.
  apply:(@euclidean_interval_rectangle_diameter_bound R (U i.1) (U i.2) s (ltW hs)).
  - by rewrite (hWidth _ (hMember i.1)).
  - by rewrite (hWidth _ (hMember i.2)).
have hBound:=@finite_planar_scaled_tube_cover_bound R I W Q (Num.sqrt 2) s
  (sqrtr_ge0 _) hs hCover hDiameter.
have hCard:(#|I|=N*N)%N by rewrite /I card_prod !card_ord.
rewrite hCard natrM in hBound.
have hWeight:=@power_cantor_uniform_level_weight_count R c m J n H j s hc hm hm1 hJ hTree hWidth.
have hCount:((N%:R)^+2*s=real_power s (1-2 * m))%R.
  apply:(@power_cantor_square_scaled_count R m s N hs).
  exact hWeight.
have hAlgebra:((N%:R*N%:R)*euclidean_unit_ball_volume R 2*(Num.sqrt 2+1)^+2/2*s)%R=
    ((euclidean_unit_ball_volume R 2*(Num.sqrt 2+1)^+2/2)*((N%:R)^+2*s))%R by ring.
by rewrite hAlgebra hCount in hBound.
Qed.
