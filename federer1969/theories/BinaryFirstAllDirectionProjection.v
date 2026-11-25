(** Federer (1969), 3.3.20, p. 307: full actual first-level projections in every unit direction. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EqualCostIntervalTreeUP
  SpecialIntervalFamilyUP BinaryCantorSquareLevelsUP BinaryCantorOriginalFirstProjection
  BinaryFirstFactorReflection SquareLevelFactorUnion SymmetricSquareAbsoluteProjectionImage SymmetricSquareScalarProjections
  EuclideanInnerProduct InnerMetric EuclideanRealPlane EuclideanCantorProduct EuclideanIntervalRectangles BinaryCantorAllDirectionProjection RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_original_all_direction_first_full_projection]:
    the actual original first refinement fills the full projected root interval
    exactly on the entire printed U, 3.3.20, p. 307. Reflection
    of the ACTUAL original first-level factor and coordinate interchange reduce
    all signs and directions to the proved original overlap theorem.
    The shift gives the unchanged signed root endpoints. *)
Theorem binary_original_all_direction_first_full_projection (R:realType) (c m u v:R)
    (J:compact_real_intervals R) H G:
  0<c ->0<m ->m<1 ->u^+2+v^+2= 1 ->val J=(`[0,1]:set (real_line_metric R)) ->
  is_equal_cost_interval_tree (fun t=>c * real_power t m) J (fun _:nat=>2%N) H ->
  is_binary_cantor_square_levels H G ->
  ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
      (\bigcup_(D in [set` G 1%N]) euclidean_interval_rectangle D.1 D.2)=
    (fun t:R=>t+(u-`|u|+v-`|v|)/2) @` (`[0,`|u|+ `|v|]:set R) <->
    binary_full_projection_direction (real_power 2 (-m^-1)) u v).
Proof.
move=>hc hm hm1 hUnit hJ hTree hG.
pose A:=\bigcup_(S in [set` H 1%N]) val S.
rewrite (@binary_original_square_level_factor_union R H G hG 1%N).
have hReflection:=@binary_original_first_factor_reflection R c m J H hc hm hm1 hJ hTree.
rewrite (symmetric_square_absolute_projection_image u v hReflection).
have hCancel (B C:set R) (a:R):
    ((fun t:R=>t+a) @` B=(fun t:R=>t+a) @` C) <->B=C.
  split;last by move=>->.
  move=>hEqual;apply/seteqP;split=>x hx.
  - have hy:((fun t:R=>t+a) @` C) (x+a) by rewrite -hEqual;exists x.
    have [y hMember hYX]:=hy.
    have hY:y=x by apply:(addIr a);exact:hYX.
    by rewrite -hY.
  - have hy:((fun t:R=>t+a) @` B) (x+a) by rewrite hEqual;exists x.
    have [y hMember hYX]:=hy.
    have hY:y=x by apply:(addIr a);exact:hYX.
    by rewrite -hY.
rewrite hCancel /binary_full_projection_direction.
have hAbs:`|u|^+2 + `|v|^+2= 1 by rewrite -!normrX !ger0_norm ?sqr_ge0.
case:(leP `|v| `|u|)=>hOrder.
- have hu:0<`|u|.
    have h0:=normr_ge0 u;have h1:=normr_ge0 v.
    case:(ltP 0 `|u|)=>//hNo;have hZ:`|u|=0 by lra.
    have hZV:`|v|=0 by lra.
    nra.
  rewrite ?(max_l hOrder) ?(min_r hOrder).
  rewrite -(@binary_original_square_level_factor_union R H G hG 1%N).
  exact:(@binary_cantor_original_first_projection_overlap R c m `|u| `|v| J H G
    hc hm hm1 hu (normr_ge0 v) hOrder hJ hTree hG).
- have hv:0<`|v| :=le_lt_trans (normr_ge0 u) hOrder.
  rewrite ?(max_r (ltW hOrder)) ?(min_l (ltW hOrder))
    (square_scalar_projection_swap A `|u| `|v|) [in `[0,`|u|+ `|v|]]addrC.
  rewrite -(@binary_original_square_level_factor_union R H G hG 1%N).
  exact:(@binary_cantor_original_first_projection_overlap R c m `|v| `|u| J H G
    hc hm hm1 hv (normr_ge0 u) (ltW hOrder) hJ hTree hG).
Qed.
