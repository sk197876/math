(** Federer (1969), 3.3.4, p. 292: both directions of an actual
    projective fibre lie in the original coordinate kernel. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanOrthogonalAdjointInverse EuclideanBlockCoordinates EuclideanBlockLinearMaps
  CoordinateProjection EuclideanCoordinateMetric StructureActiveCoordinatesUP StructureActiveProjection
  StructureDirectionMapUP StructureProjectiveSpace StructureDirectionKernel
  InnerUnitNormalization SymmetricSquareGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [structure_active_direction_fibre_kernel]: Federer
    3.3.4, p. 292, supporting F inverse R contained in D.
    Equality in the actual projective carrier retains both antipodal
    directions. The exact inverse coordinates, rather than a supplied
    kernel-containment hypothesis, imply vanishing of the first m
    coordinates of the original ambient vector. *)
Theorem structure_active_direction_fibre_kernel (R:realType) (X:metricType R) m k
    (j:'I_k) (w:Hom (R_n R (1+m)) (R_n R (m+k)))
    (q:X->inner_metric_space (@euclidean_inner_productP R m.+1))
    (f:X->structure_projective_space R m)
    (h:Hom (R_n R m.+1) (R_n R m.+1))
    (z:structure_projective_space R m) (x:X) (y:R_n R (m+k)):
  is_structure_active_inclusion j w ->is_structure_projective_direction_map q f ->
  is_orthogonal_map (@euclidean_inner_product R m.+1)
    (@euclidean_inner_product R m.+1) (hom_as_linear h) ->
  val z=inner_projective_square (h (@coordinate_basis R m.+1 (lshift m (ord0:'I_1)))) ->
  euclidean_rectangular_adjoint w y=euclidean_rectangular_adjoint h (q x) ->
  0<inner_norm (@euclidean_inner_productP R m.+1) (q x) ->f x=z ->
  @euclidean_first_block R m k y=0.
Proof.
move=>hW hF hH hz hProjection hx hValue.
pose i0:=lshift m (ord0:'I_1).
pose v:=h (@coordinate_basis R m.+1 i0).
pose L:=hom_comp (@euclidean_last_block_map R 1 m) (euclidean_rectangular_adjoint h).
have hUnit:inner_norm (@euclidean_inner_productP R m.+1) v= 1.
  rewrite /v (orthogonal_map_norm (@euclidean_inner_productP R m.+1)
    (@euclidean_inner_productP R m.+1) hH).
  exact:euclidean_coordinate_unit_norm.
have hKernel:L v=0.
  rewrite /L /v hom_compE (euclidean_orthogonal_adjoint_cancel hH).
  apply/ffunP=>i; rewrite /euclidean_last_block_map /euclidean_last_block
    ffunE /coordinate_basis ffunE.
  by rewrite /i0 (@eq_rlshift 1 m i (ord0:'I_1)) ffunE.
have hSquare:inner_projective_square
    (inner_unit_normalization (@euclidean_inner_productP R m.+1) (q x))=inner_projective_square v.
  by rewrite -(hF.2 x hx) hValue hz.
have hZero:=@structure_direction_fibre_kernel R (R_n R m.+1) (R_n R m)
    (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1)
    (hom_as_linear L) (q x) v hx hUnit hKernel hSquare.
have hTail:@euclidean_last_block R 1 m (euclidean_rectangular_adjoint h (q x))=
    @euclidean_first_block R m k y.
  rewrite -hProjection (structure_active_projection_coordinates hW y).
  apply/ffunP=>i; by rewrite /euclidean_last_block ffunE euclidean_block_join_right.
change (@euclidean_last_block R 1 m (euclidean_rectangular_adjoint h (q x))=0) in hZero.
by rewrite -hTail.
Qed.
