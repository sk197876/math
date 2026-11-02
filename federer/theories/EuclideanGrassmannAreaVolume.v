(** Federer (1969), 3.2.28(4), p. 267:
    the oriented Grassmann volume is twice the
    actual unoriented square Grassmann volume. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanLinearMaps
  InnerProductUP InnerNorm InnerMetric ExteriorGrading ExteriorNorm InnerExterior InnerExteriorPositivity
  AssociatedSubspace SimpleElementary FiniteExteriorPowers FiniteOrdinalBasis
  InnerSymmetricPositivity SymmetricSquareGeometry SymmetricSquareManifoldArea
  FiniteInnerSmoothSubmanifoldUP EuclideanOrientedGrassmannSmooth EuclideanGrassmannSquare HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_grassmann_area_volume]: the
    displayed equality H^r(Go(n,m))=2 H^r(G(n,m)),
    Federer 3.2.28(4), p. 267, where
    r=m(n-m). It follows from the actual
    square-map area theorem, not from a quotient
    measure definition. Positive m is retained. *)
Theorem euclidean_grassmann_area_volume (R:realType) m n:
  (0<m)%N ->(m<=n)%N ->
  let E:=exterior_power (R_n R n) m in
  let B:=@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m in
  let hB:=@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m in
  @hausdorff_measure R (inner_metric_space hB) (m*(n-m))
    [set x|simple x /\exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) x= 1%R]=
    (2:R)%:E* @hausdorff_measure R (inner_metric_space (@symmetric_inner_productP R E B hB 2)) (m*(n-m))
      (@euclidean_grassmann_square_set R n m).
Proof.
Local Open Scope ring_scope.
move=>hm hmn E B hB.
pose A:set E:=[set x|simple x /\inner_norm hB x= 1].
have hb:=finite_ordinal_basis (@finite_e_lambda_basis R n (R_n R n)
  (@coordinate_basis R n) (@coordinate_basisP R n) (euclidean_two_nonzero R) m).
have hMan:=inner_smooth_submanifold_class (@euclidean_oriented_grassmann_smooth_submanifold R m n hm hmn) 1%N.
have hUnit x (hx:A x):inner_norm hB x= 1:=hx.2.
have hAnti x (hx:A x):A (-x).
  split.
  - have hs:=@simple_scale R (R_n R n) m x (-1) hm hx.1.
    by rewrite scaleN1r in hs.
  - by rewrite inner_normN; exact:hx.2.
rewrite euclidean_grassmann_square_image.
exact:(@inner_projective_square_manifold_area R E B hB _ _ hb (m*(n-m)) 1 A
  (leqnn 1) hMan hUnit hAnti).
Qed.
