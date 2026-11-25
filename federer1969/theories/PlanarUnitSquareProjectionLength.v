(** Federer (1969), 3.3.20, p. 307: exact original root-square projection length in all directions. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge EuclideanInnerProduct InnerMetric
  EuclideanRealPlane EuclideanIntervalRectangles EuclideanCantorProduct EuclideanRectangleScalarProjection
  SymmetricSquareAbsoluteProjection SymmetricSquareAbsoluteProjectionImage
  PositiveAffineClosedSegment LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [planar_original_unit_square_projection_length]:
    L^1(P_u(I times I))=|u_1|+|u_2|, 3.3.20, p. 307.
    Actual root reflection and the proved nonnegative rectangle
    projection formula retain every coefficient sign and zero coordinate. *)
Lemma planar_original_unit_square_projection_length (R:realType) (J:compact_real_intervals R) (u v:R):
  val J=(`[0,1]:set (real_line_metric R)) ->
  lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
      euclidean_interval_rectangle J J)=(`|u|+ `|v|)%:E.
Proof.
move=>hJ.
have hReflection x:val J x <->val J (1-x).
  rewrite hJ /= !in_itv /=;split=>/andP[h0 h1];apply/andP;split;lra.
change (lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
      euclidean_cantor_product (val J) (val J))=(`|u|+ `|v|)%:E).
rewrite (symmetric_square_absolute_projection_length u v hReflection).
have hProjection:=@euclidean_rectangle_scalar_projection R J J 0 1 0 1 `|u| `|v|
  ler01 ler01 (normr_ge0 u) (normr_ge0 v) hJ hJ.
rewrite !mulr0 add0r !mulr1 in hProjection.
rewrite hProjection lebesgue_scalar_segment ?subr0 //.
exact:addr_ge0 (normr_ge0 u) (normr_ge0 v).
Qed.

(** Source for [planar_original_unit_square_projection_interval]:
    the full signed original root-square projection interval,
    supporting the c_u=1 locus of 3.3.20, p. 307. Actual
    reflection translates the positive-coordinate root interval. *)
Lemma planar_original_unit_square_projection_interval (R:realType) (J:compact_real_intervals R) (u v:R):
  val J=(`[0,1]:set (real_line_metric R)) ->
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
      euclidean_interval_rectangle J J=
    (`[(u-`|u|+v-`|v|)/2,(u-`|u|+v-`|v|)/2+ `|u|+ `|v|]:set R).
Proof.
move=>hJ.
have hReflection x:val J x <->val J (1-x).
  rewrite hJ /= !in_itv /=;split=>/andP[h0 h1];apply/andP;split;lra.
change ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @`
    euclidean_cantor_product (val J) (val J)=
    (`[(u-`|u|+v-`|v|)/2,(u-`|u|+v-`|v|)/2+ `|u|+ `|v|]:set R)).
rewrite (symmetric_square_absolute_projection_image u v hReflection).
have hProjection:=@euclidean_rectangle_scalar_projection R J J 0 1 0 1 `|u| `|v|
  ler01 ler01 (normr_ge0 u) (normr_ge0 v) hJ hJ.
rewrite !mulr0 add0r !mulr1 in hProjection.
rewrite hProjection.
have hShift:(fun t:R=>t+(u-`|u|+v-`|v|)/2)=
    (fun t:R=>(u-`|u|+v-`|v|)/2+1 * t) by apply:funext=>t;lra.
rewrite hShift positive_affine_closed_segment_image // !mul1r ?add0r ?addr0.
by rewrite addrA.
Qed.
