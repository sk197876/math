(** Federer (1969), 3.3.20, p. 307: actual four-square scalar projection union. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground CompactIntervalGauge EuclideanInnerProduct
  InnerMetric EuclideanRealPlane EuclideanIntervalRectangles BinaryCantorFirstLevelSelection
  EuclideanRectangleScalarProjection BinaryProjectedIntervalOverlap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_corner_original_projection_union]: the actual
    scalar projection of the original four first-level squares is the
    four closed intervals displayed in 3.3.20, p. 307. The exact
    original cell-coordinate laws prove this set identity; no overlap,
    nullity or interval-image conclusion is assumed. *)
Theorem binary_corner_original_projection_union (R:realType) (s u v:R)
    (F:{fset (compact_real_intervals R*compact_real_intervals R)})
    (Q:bool*bool->compact_real_intervals R*compact_real_intervals R):
  0<s ->0<=u ->0<=v ->(forall k,Q k \in F) ->
  (forall S,S \in F ->exists k,S=Q k) ->
  (forall k,val (Q k).1=(`[binary_first_level_coordinate s k.1,
      binary_first_level_coordinate s k.1+s]:set (real_line_metric R)) /\
    val (Q k).2=(`[binary_first_level_coordinate s k.2,
      binary_first_level_coordinate s k.2+s]:set (real_line_metric R))) ->
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
    (\bigcup_(P in [set` F]) euclidean_interval_rectangle P.1 P.2)=
    binary_projected_interval_union s u v.
Proof.
move=>hs hu hv hMembers hExhaust hCoordinates.
pose P:=fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
  u * euclidean_real_plane_first p+v * euclidean_real_plane_second p.
have hImage b d:P @` euclidean_interval_rectangle (Q (b,d)).1 (Q (b,d)).2=
    (`[u * binary_first_level_coordinate s b+v * binary_first_level_coordinate s d,
      u * (binary_first_level_coordinate s b+s)+v * (binary_first_level_coordinate s d+s)]:set R).
  apply:euclidean_rectangle_scalar_projection=>//;try exact:(hCoordinates (b,d)).1;
    try exact:(hCoordinates (b,d)).2;lra.
have hCell b d:P @` euclidean_interval_rectangle (Q (b,d)).1 (Q (b,d)).2=
    (if b then (if d then (`[(1-s)*(u+v),u+v]:set R)
      else (`[(1-s)*u,u+s*v]:set R))
    else (if d then (`[(1-s)*v,s*u+v]:set R) else (`[0,s*(u+v)]:set R))).
  rewrite hImage;case:b;case:d;rewrite /binary_first_level_coordinate /=;
    apply/seteqP;split=>z;rewrite /= !in_itv /=;
    move=>/andP[h0 h1];apply/andP;split;nra.
apply/seteqP;split=>z.
- move=>[x [S hS hxS] hValue].
  have [[b d] hSValue]:=hExhaust S hS.
  have hz:(P @` euclidean_interval_rectangle (Q (b,d)).1 (Q (b,d)).2) z.
    exists x;first by rewrite -hSValue.
    exact:hValue.
  clear hSValue.
  rewrite hCell in hz;move:hz;case:b;case:d=>/=hz;
    [right|left;right|left;left;right|left;left;left];exact:hz.
- have hLift b d:
      (P @` euclidean_interval_rectangle (Q (b,d)).1 (Q (b,d)).2) z ->
      (P @` (\bigcup_(S in [set` F]) euclidean_interval_rectangle S.1 S.2)) z.
    move=>[x hx hValue];exists x=>//;exists (Q (b,d));[exact:hMembers|exact:hx].
  move=>[[[hz|hz]|hz]|hz].
  + apply:(hLift false false);by rewrite hCell.
  + apply:(hLift false true);by rewrite hCell.
  + apply:(hLift true false);by rewrite hCell.
  + apply:(hLift true true);by rewrite hCell.
Qed.
