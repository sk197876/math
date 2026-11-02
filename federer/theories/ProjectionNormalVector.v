(** Supporting the normal-frame wedge in Federer (1969), 2.10.16, p. 178.
    The adjoint of an orthogonal projection carries the standard unit top
    vector to a simple unit vector of its normal space. Use the abstract
    adjoint of 1.7.4, pp. 30–31, and the exterior isometry laws of 1.7.5, p.
    32. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanProjectionSpace EuclideanProjectionMetric CoordinateProjection
  InnerProductUP OrthogonalMaps AdjointUP Adjoint ProjectionCriteria OrthogonalInjectionSpaces
  OrthonormalFamilies ExteriorGrading FiniteExteriorPowers AssociatedSubspace ExteriorMaps ExteriorDeterminant ExteriorNorm
  ExteriorNormNaturality ExteriorOperatorEstimate SimpleElementary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_coordinate_top_vector_unit]: supporting
    standard unit top vector for 2.10.16, p. 178, from
    the orthonormal-product law in 1.7.5, p. 32.
    The empty product in degree zero also has norm one. *)
Lemma euclidean_coordinate_top_vector_unit (R : realType) (m : nat) :
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m)
    (@top_vector R m (R_n R m) (@coordinate_basis R m))= 1.
Proof.
change (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m)
  (e_lambda (@coordinate_basis R m) (ord_tuple m))= 1).
have ho : orthonormal_family (@euclidean_inner_product R m) (@coordinate_basis R m).
  by move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE eq_sym.
exact (@orthonormal_product_unit_norm R (euclidean_two_nonzero R) (R_n R m)
  (@euclidean_inner_product R m) (@euclidean_inner_productP R m) m (@coordinate_basis R m) ho).
Qed.

(** Source for [projection_normal_vector]: supporting oriented
    normal m-vector for the coordinate calculation of
    2.10.16, p. 178. It is the exterior image of the
    standard top vector under the existing abstract adjoint. *)
Definition projection_normal_vector (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m) :=
  exterior_power_map (inner_adjoint (@euclidean_inner_productP R n)
    (@euclidean_inner_productP R m) (@coordinate_basisP R n) (euclidean_projection_linear p)) m
    (@top_vector R m (R_n R m) (@coordinate_basis R m)).
Arguments projection_normal_vector {R n m} p.

(** Source for [projection_normal_adjoint_orthogonal]: supporting
    adjoint isometry for 2.10.16, p. 178, exactly the
    projection-adjoint characterisation of 1.7.4, pp. 30–31. *)
Lemma projection_normal_adjoint_orthogonal (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m) :
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) (euclidean_projection_linear p)).
Proof.
have ha := inner_adjointP (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  (@coordinate_basisP R n) (euclidean_projection_linear p).
exact ((@projection_iff_adjoint_orthogonal R (R_n R n) (R_n R m) _ _
  (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
  (euclidean_projection_linear p) _ ha).1 (orthogonal_projection_map_projection p)).
Qed.

(** Source for [projection_normal_vectorE]: supporting explicit
    normal-frame product for 2.10.16, p. 178. The
    exterior functor sends the standard ordered product to
    the ordered product of its adjoint images, by 1.3.1,
    pp. 12–13. This is an evaluation law, not a construction
    exposed to replace the abstract adjoint specification. *)
Lemma projection_normal_vectorE (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m) :
  projection_normal_vector p=e_lambda
    (fun i => inner_adjoint (@euclidean_inner_productP R n) (@euclidean_inner_productP R m)
      (@coordinate_basisP R n) (euclidean_projection_linear p) (@coordinate_basis R m i)) (ord_tuple m).
Proof.
rewrite /projection_normal_vector /top_vector /finite_e_lambda /=.
exact: exterior_map_indexed_product.
Qed.

(** Source for [projection_normal_vector_simple]: supporting
    simple normal vector in 2.10.16, p. 178, by the
    product definition of simplicity in 1.6.1, pp. 23–24. *)
Lemma projection_normal_vector_simple (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m) : simple (projection_normal_vector p).
Proof. rewrite projection_normal_vectorE; exact: product_simple. Qed.

(** Source for [projection_normal_vector_unit]: supporting unit
    normal vector in 2.10.16, p. 178. The orthogonal
    adjoint preserves the standard top norm by 1.7.5,
    p. 32; there is no positive-degree restriction. *)
Lemma projection_normal_vector_unit (R : realType) (n m : nat)
    (p : orthogonal_projection_metric_space R n m) :
  exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) (projection_normal_vector p)= 1.
Proof.
rewrite /projection_normal_vector
  (@exterior_norm_orthogonal_natural R (euclidean_two_nonzero R) (R_n R m) (R_n R n)
    _ _ (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) _
    (projection_normal_adjoint_orthogonal p) m _).
exact: euclidean_coordinate_top_vector_unit.
Qed.
