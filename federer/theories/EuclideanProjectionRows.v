(** Expanded continuity support for Federer (1969), 3.2.45,
    p. 279: connect the actual projection-space metric to
    scalar rows through the existing adjoint and Hom interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerNorm
  InnerProductUP Bilinear CoordinateProjection EuclideanCoordinateMetric OrthogonalMaps
  Adjoint AdjointUP HomInner MetricSubsetBackground OrthogonalInjectionSpaces
  EuclideanProjectionSpace EuclideanProjectionMetric ProjectionNormalVector EuclideanRowFamily EuclideanRowNormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_projection_rows]: the actual scalar
    rows of the original projections in Federer 3.2.45,
    p. 279, expressed through the adjoint of 1.7.4, p. 30.
    This abbreviates the existing opaque adjoint and selects no
    new inverse or coordinate representation. *)
Definition euclidean_projection_rows (R : realType) n m
    (p : orthogonal_projection_metric_space R n m) (i : 'I_m) : R_n R n :=
  inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
    (@coordinate_basisP R n) (euclidean_projection_linear p) (@coordinate_basis R m i).

(** Source for [euclidean_projection_rows_laws]: the independent
    scalar-row laws for the actual projections, by the adjoint
    equation of 1.7.4, p. 30; supporting Federer 3.2.45,
    p. 279. No property of an adjoint construction is used. *)
Lemma euclidean_projection_rows_laws (R : realType) n m
    (p : orthogonal_projection_metric_space R n m) :
  is_euclidean_row_family (euclidean_projection_rows p) (euclidean_projection_linear p).
Proof.
move=> x i; rewrite /euclidean_projection_rows.
have h := @inner_adjointP R (R_n R n) (R_n R m)
  (@euclidean_inner_product R n) (@euclidean_inner_product R m)
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n) (euclidean_projection_linear p)
  x (@coordinate_basis R m i).
by rewrite euclidean_inner_basis in h; symmetry.
Qed.

(** Source for [euclidean_projection_row_norm]: actual projection
    rows have norm one, by the adjoint isometry in Federer
    1.7.4, pp. 30–31; supporting 3.2.45, p. 279. A row
    index already excludes an empty target basis. *)
Lemma euclidean_projection_row_norm (R : realType) n m
    (p : orthogonal_projection_metric_space R n m) (i : 'I_m) :
  inner_norm (@euclidean_inner_productP R n) (euclidean_projection_rows p i) = 1.
Proof.
rewrite /euclidean_projection_rows.
rewrite (@orthogonal_map_norm R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  _ (projection_normal_adjoint_orthogonal p)).
exact: euclidean_coordinate_unit_norm.
Qed.

(** Source for [euclidean_projection_row_difference_bound]: expanded
    support for Federer 3.2.45, p. 279. The existing Hom metric
    bounds each actual row difference, by adjoint operator-norm
    equality and 1.7.9, p. 35. The projection-space metric is
    its original restricted Hom metric, not a replacement. *)
Lemma euclidean_projection_row_difference_bound (R : realType) n m
    (p q : orthogonal_projection_metric_space R n m) (i : 'I_m) :
  inner_norm (@euclidean_inner_productP R n)
    (euclidean_projection_rows p i-euclidean_projection_rows q i) <= mdist p q.
Proof.
pose D : Hom (R_n R n) (R_n R m) := orthogonal_projection_map p-orthogonal_projection_map q.
pose v (j : 'I_m) := euclidean_projection_rows p j-euclidean_projection_rows q j.
have hD : is_euclidean_row_family v (hom_as_linear D).
  move=> x j; rewrite /D hom_as_linearE -[-orthogonal_projection_map q]scaleN1r
    hom_addE hom_scaleE scaleN1r !ffunE.
  change (euclidean_projection_linear p x j-euclidean_projection_linear q x j =
    euclidean_inner_product x (v j)).
  by rewrite !euclidean_projection_rows_laws /v (bilBr (inner_bilinear (@euclidean_inner_productP R n))).
have h := @euclidean_row_family_hom_norm_bound R n m v D hD i.
change (inner_norm (@euclidean_inner_productP R n) (v i) <=
  hom_norm (@euclidean_inner_productP R n) (@euclidean_inner_productP R m) (@coordinate_basisP R n) D).
exact h.
Qed.
