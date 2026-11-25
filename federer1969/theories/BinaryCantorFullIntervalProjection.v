(** Federer (1969), 3.3.20, p. 307: original Cantor-square projections in the overlap locus. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  EqualCostIntervalTreeSpecial SpecialIntervalFamilyUP PowerConcaveIntervalGauge
  BinaryCantorSquareLevelsUP BinaryCantorSquareLevelTopology BinaryCantorOriginalFirstProjection
  BinaryCantorParentProjectionSurvival EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanIntervalRectangles EuclideanCantorProduct EuclideanRectangleScalarProjection
  PlanarScalarProjectionContinuity CompactNestedProjectionImage RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_cantor_square_full_interval_projection]:
    for every direction in the printed overlap locus, the projection
    of the ORIGINAL E equals its full endpoint interval, 3.3.20,
    p. 307. Original parent similarities prove every finite-level
    image unchanged; decreasing compact fibres and continuity pass to
    the actual original intersection. No projection surjectivity or
    replacement Cantor set is a premise. *)
Theorem binary_original_cantor_square_full_interval_projection (R:realType) (c m u v:R)
    (J:compact_real_intervals R) H G (A:set (real_line_metric R)):
  0<c ->0<m ->m<1 ->0<u ->0<=v ->v<=u ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  (1-2 * real_power 2 (-m^-1)) * u<=v ->
  (1-2 * real_power 2 (-m^-1)) * v<=real_power 2 (-m^-1) * u ->
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
    euclidean_cantor_product A A=(`[0,u+v]:set R).
Proof.
move=>hc hm hm1 hu hv hvu hJ hTree hA hG hMiddle hSide.
pose X:=inner_metric_space (@euclidean_inner_productP R 2).
pose P:=fun p:X=>u * euclidean_real_plane_first p+v * euclidean_real_plane_second p.
pose C j:=\bigcup_(D in [set` G j]) euclidean_interval_rectangle D.1 D.2.
have hSpecial:=@equal_cost_interval_tree_special R _ (power_concave_interval_gauge hc hm hm1)
  J (fun _:nat=>2%N) H hTree.
have hDecrease n k:(n<=k)%N ->C k `<=` C n.
  exact:(@binary_original_square_level_union_decreasing R _ H G hSpecial hG n k).
have hRoot:C 0%N=euclidean_interval_rectangle J J.
  apply/seteqP;split=>x.
  - move=>[D hD hx];change (is_true (D \in G 0%N)) in hD.
    move:hD;rewrite hG (equal_cost_tree_root hTree) in_fsetM !in_fset1=>/andP[/eqP h0 /eqP h1].
    case:D h0 h1 hx=>S T /= -> ->;by [].
  - move=>hx;exists (J,J);last exact:hx.
    by change (is_true ((J,J) \in G 0%N));rewrite hG (equal_cost_tree_root hTree) in_fsetM !in_fset1 eqxx.
have hRootImage:P @` C 0%N=(`[0,u+v]:set R).
  rewrite hRoot.
  have h:=@euclidean_rectangle_scalar_projection R J J 0 1 0 1 u v
    ler01 ler01 (ltW hu) hv hJ hJ.
  by rewrite !mulr0 add0r !mulr1 in h.
have hFirst:P @` C 1%N=(`[0,u+v]:set R).
  apply:(@binary_cantor_original_first_projection_overlap R c m u v J H G
    hc hm hm1 hu hv hvu hJ hTree hG).2;by split.
have hSurvive:=@binary_original_parent_projection_survival R c m u v J H G A
  hc hm hm1 (ltW hu) hv hJ hTree hA hG hFirst.
have hImages:forall j,P @` C j=(`[0,u+v]:set R).
  elim=>[|j ih];first exact:hRootImage.
  apply/seteqP;split=>z.
  - move=>[x hx hValue].
    have hz:(P @` C 0%N) z by exists x=>//;exact:hDecrease 0%N j.+1 (leq0n _) x hx.
    by rewrite hRootImage in hz.
  - move=>hz;have hzOld:(P @` C j) z by rewrite ih.
    have [x [D hD hx] hValue]:=hzOld.
    change (is_true (D \in G j)) in hD.
    move:hD;rewrite hG in_fsetM=>/andP[hS hT].
    apply:(hSurvive j D.1 D.2 hS hT z).
    by exists x.
have hLimit:=@compact_nested_continuous_image_intersection R X [the metricType R of real_line_metric R]
  C P (@original_square_level_union_compact R (G 0%N))
  (fun j=>@original_square_level_union_closed R (G j)) hDecrease
  (@planar_scalar_original_projection_continuous R u v).
have hOriginal:euclidean_cantor_product A A=\bigcap_j C j
  :=@binary_original_square_limit_identity R H G A hA hG.
rewrite -hOriginal in hLimit.
rewrite hLimit;apply/seteqP;split=>z.
- move=>hz;have h:=hz 0%N Logic.I;by rewrite hImages in h.
- move=>hz j _;by rewrite hImages.
Qed.
