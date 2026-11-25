(** Supporting the integral-geometric product assertion in Federer (1969),
    2.10.46, p. 204. Freilich (1950), Theorem 4.5, Parts 1–5, pp. 242–247,
    reduces a projected cylinder to a scalar affine coordinate above a
    lower-dimensional projection. We use the abstract adapted orthogonal
    chart already established from Federer's 1.7.4, pp. 30–31. No new choice
    of coordinates is exposed. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric InnerNorm OrthogonalMaps CoordinateProjection EuclideanCoordinateMetric
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinear
  EuclideanRightBlockProjection OrthogonalProjectionChartUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_first_block_line]: supporting affine
    line parametrisation for Federer 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Parts 1–4,
    pp. 242–247. The scalar coordinate is placed first
    in the project's Cartesian convention, an orthogonal reordering
    of the source's last coordinate. *)
Lemma euclidean_first_block_line (R : realType) n (y : R_n R n) (t : R) :
  @euclidean_block_join R 1 n (euclidean_one_embed t,y)=
    t*:(@coordinate_basis R (1+n) (lshift n (ord0 : 'I_1)))+
    @euclidean_block_join R 1 n (0,y).
Proof.
apply: euclidean_block_vectors_ext.
- move=> i; rewrite (ord1 i) euclidean_block_join_left /euclidean_one_embed ffunE
    ffunE euclidean_block_join_left /coordinate_basis !ffunE eqxx.
  change (t=t*1+0); by rewrite mulr1 addr0.
- move=> i; rewrite euclidean_block_join_right ffunE euclidean_block_join_right
    /coordinate_basis !ffunE eq_rlshift.
  change (y i=t*0+y i); by rewrite mulr0 add0r.
Qed.

(** Source for [projection_chart_line_kernel]: supporting
    scalar normal coordinate for 2.10.46, p. 204;
    Freilich (1950), Theorem 4.5, Parts 2–3,
    pp. 243–245. In a chart adapted to a
    codimension-one projection, its kernel occupies the first axis. *)
Lemma projection_chart_line_kernel (R : realType) k
    (p : {linear R_n R (1+k) -> R_n R k})
    (c d : {linear R_n R (1+k) -> R_n R (1+k)}) (z : R_n R (1+k)) :
  is_orthogonal_projection_chart p c d -> p z=0 ->
  c z=(c z (lshift k (ord0 : 'I_1)))*:(@coordinate_basis R (1+k) (lshift k ord0)).
Proof.
move=> hc hz; apply: euclidean_block_vectors_ext.
- move=> i; rewrite (ord1 i) ffunE /coordinate_basis ffunE eqxx.
  change (c z (lshift k ord0)=c z (lshift k ord0)*1); by rewrite mulr1.
- move=> i; have he := congr1 (fun v : R_n R k=>v i) (projection_chart_coordinate_law hc z).
  rewrite hz /euclidean_right_block /euclidean_block_split !ffunE in he.
  rewrite he ffunE /coordinate_basis ffunE eq_rlshift.
  change (0=c z (lshift k ord0)*0); by rewrite mulr0.
Qed.

(** Source for [projection_chart_line_kernel_norm]: supporting
    nondegenerate scalar stretching factor for 2.10.46,
    p. 204; Freilich (1950), Theorem 4.5,
    Parts 2–3, pp. 243–245. The absolute scalar
    coordinate equals the Euclidean norm, without choosing its sign. *)
Lemma projection_chart_line_kernel_norm (R : realType) k
    (p : {linear R_n R (1+k) -> R_n R k})
    (c d : {linear R_n R (1+k) -> R_n R (1+k)}) (z : R_n R (1+k)) :
  is_orthogonal_projection_chart p c d -> p z=0 ->
  `|c z (lshift k (ord0 : 'I_1))|=inner_norm (@euclidean_inner_productP R (1+k)) z.
Proof.
move=> hc hz.
have he := @orthogonal_map_norm R (R_n R (1+k)) (R_n R (1+k))
  (@euclidean_inner_product R (1+k)) (@euclidean_inner_product R (1+k))
  (@euclidean_inner_productP R (1+k)) (@euclidean_inner_productP R (1+k)) c
  (projection_chart_orthogonal_law hc) z.
by rewrite (projection_chart_line_kernel hc hz) inner_normZ euclidean_coordinate_unit_norm mulr1 in he.
Qed.

(** Source for [line_cylinder_projection_coordinates]: supporting
    affine fibre formula for the integral-geometric assertion in
    2.10.46, p. 204; Freilich (1950), Theorem
    4.5, Parts 1–5, pp. 242–247. The right
    coordinate is q(y), while the left coordinate is a*t+b(y).
    Only the abstract chart and common-factor equations are used;
    the formula itself remains true for a zero stretching factor. *)
Theorem line_cylinder_projection_coordinates (R : realType) n k
    (f : {linear R_n R (1+n) -> R_n R (1+k)})
    (p : {linear R_n R (1+k) -> R_n R k})
    (q : {linear R_n R n -> R_n R k})
    (c d : {linear R_n R (1+k) -> R_n R (1+k)}) :
  is_orthogonal_projection_chart p c d ->
  (forall u y, p (f (@euclidean_block_join R 1 n (u,y)))=q y) ->
  forall t y, c (f (@euclidean_block_join R 1 n (euclidean_one_embed t,y)))=
    @euclidean_block_join R 1 k
      (euclidean_one_embed ((c (f (@coordinate_basis R (1+n) (lshift n ord0)))) (lshift k ord0)*t+
        (c (f (@euclidean_block_join R 1 n (0,y)))) (lshift k ord0)),q y).
Proof.
move=> hc hfactor t y; apply: euclidean_block_vectors_ext.
- move=> i; rewrite (ord1 i) euclidean_block_join_left /euclidean_one_embed ffunE.
  by rewrite euclidean_first_block_line !linearD !linearZ !ffunE mulrC.
- move=> i; have he := congr1 (fun v : R_n R k=>v i)
    (projection_chart_coordinate_law hc (f (@euclidean_block_join R 1 n (euclidean_one_embed t,y)))).
  rewrite hfactor /euclidean_right_block /euclidean_block_split ffunE in he.
  by rewrite euclidean_block_join_right.
Qed.
