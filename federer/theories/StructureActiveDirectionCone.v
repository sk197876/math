(** Federer (1969), 3.3.4, p. 291: the actual direction-map
    ball preimage is the original one-coordinate cone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanBlockCoordinates EuclideanBlockLinearMaps CoordinateProjection EuclideanCoordinateMetric
  StructureActiveCoordinatesUP StructureActiveProjection StructureActiveBallCone
  StructureDirectionMapUP StructureProjectiveSpace InnerUnitNormalization
  SymmetricGrading InnerSymmetricPositivity SymmetricSquareGeometry MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [structure_active_direction_ball_cone]: the exact
    preimage identity for f and F in Federer 3.3.4, p. 291.
    The original nonzero domain appears only on the ball side:
    the strict coordinate cone itself excludes its zero projection. *)
Theorem structure_active_direction_ball_cone (R:realType) (X:metricType R) m k
    (j:'I_k) (w:Hom (R_n R (1+m)) (R_n R (m+k)))
    (q:X->inner_metric_space (@euclidean_inner_productP R m.+1))
    (f:X->structure_projective_space R m)
    (h:Hom (R_n R m.+1) (R_n R m.+1))
    (z:structure_projective_space R m) (x:X) (y:R_n R (m+k)) (t:R):
  is_structure_active_inclusion j w ->
  is_structure_projective_direction_map q f ->
  is_orthogonal_map (@euclidean_inner_product R m.+1)
    (@euclidean_inner_product R m.+1) (hom_as_linear h) ->
  val z=inner_projective_square (h (@coordinate_basis R (1+m) (lshift m (ord0:'I_1)))) ->
  euclidean_rectangular_adjoint w y=euclidean_rectangular_adjoint h (q x) ->0<t ->
  (0<inner_norm (@euclidean_inner_productP R m.+1) (q x) /\ mdist z (f x)<t <->
    ((t^-1)^+2-1)*
      (inner_norm (@euclidean_inner_productP R m) (@euclidean_first_block R m k y))^+2<
      ((@euclidean_last_block R m k y) j)^+2).
Proof.
move=>hW hF hH hz hProjection ht.
have hCoordinates:=structure_active_projection_coordinates hW y.
have hTail:@euclidean_last_block R 1 m (euclidean_rectangular_adjoint h (q x))=
    @euclidean_first_block R m k y.
  rewrite -hProjection hCoordinates; apply/ffunP=>i.
  by rewrite /euclidean_last_block ffunE euclidean_block_join_right.
have hFirst:(euclidean_rectangular_adjoint h (q x)) (lshift m (ord0:'I_1))=
    (@euclidean_last_block R m k y) j.
  rewrite -hProjection hCoordinates.
  rewrite (@euclidean_block_join_left R 1 m
    ([ffun _: 'I_1=>y (rshift m j)],@euclidean_first_block R m k y) (ord0:'I_1)).
  by rewrite /euclidean_last_block !ffunE.
have hCone:=@structure_active_projective_ball_cone R m h (q x) t hH ht.
rewrite hTail hFirst in hCone.
split.
- move=>[hx hBall]; apply:hCone.1; split=>//.
  move:hBall; rewrite metric_sym metric_subset_distanceE.
  by rewrite (hF.2 x hx) hz.
- move=>hAngle; have [hx hBall]:=hCone.2 hAngle; split=>//.
  rewrite metric_sym metric_subset_distanceE (hF.2 x hx) hz.
  exact:hBall.
Qed.
