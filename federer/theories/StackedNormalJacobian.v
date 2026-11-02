(** Supporting the angular constant in Federer (1969), 2.10.16, p. 178. The
    normal Jacobian of the stacked projection pair is the norm of the wedge
    of its two unit normal vectors. This uses the block-adjoint laws (1.7.4,
    p. 30), concatenated exterior products (1.6.1, p. 24), and the
    top-degree norm law (1.7.6, p. 34). *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps EuclideanProjectionSpace EuclideanProjectionMetric InnerMetric
  Adjoint StackedNormalFamily StackedNormalAdjoint EuclideanNormalJacobian ProjectionNormalVector
  ExteriorGrading ExteriorMaps ExteriorDeterminant ExteriorNorm ExteriorOperatorEstimate
  FiniteExteriorPowers ExteriorHomogeneousProducts ConcatenatedFamilies ConcatenatedProducts TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [stacked_normal_top_product]: supporting normal
    product identity for 2.10.16, p. 178. The top exterior
    image of the adjoint is the concatenation, in block
    order, of the two projection normal vectors. *)
Lemma stacked_normal_top_product (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q,
  exterior_power_map (inner_adjoint (@euclidean_inner_productP R n)
    (@euclidean_inner_productP R (a+r)) (@coordinate_basisP R n) (F (p,q))) (a+r)
    (@top_vector R (a+r) (R_n R (a+r)) (@coordinate_basis R (a+r)))=
    exterior_product (projection_normal_vector p) (projection_normal_vector q).
Proof.
move=> hF p q.
change (exterior_power_map (inner_adjoint (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R (a+r)) (@coordinate_basisP R n) (F (p,q))) (a+r)
  (e_lambda (@coordinate_basis R (a+r)) (ord_tuple (a+r)))=
  exterior_product (projection_normal_vector p) (projection_normal_vector q)).
rewrite exterior_map_indexed_product !projection_normal_vectorE concatenated_product.
apply (congr1 (fun e : 'I_(a+r) -> R_n R n => e_lambda e (ord_tuple (a+r)))).
apply/funext=> i; rewrite -(splitK i); case: (split i)=> j.
- rewrite concatenate_family_l; exact (@stacked_normal_adjoint_left_basis R n a r F hF p q j).
- rewrite concatenate_family_r; exact (@stacked_normal_adjoint_right_basis R n a r F hF p q j).
Qed.

(** Source for [stacked_normal_jacobian_wedge]: supporting
    angular Jacobian identity for the middle formula of
    2.10.16, p. 178. The standard top vector has unit
    norm, so 1.7.6, p. 34, turns the preceding exterior
    identity into an equality of actual nonnegative norms. *)
Theorem stacked_normal_jacobian_wedge (R : realType) (n a r : nat)
    (F : orthogonal_projection_metric_space R n a * orthogonal_projection_metric_space R n r ->
      {linear R_n R n -> R_n R (a+r)}) :
  is_stacked_normal_family F -> forall p q,
  euclidean_normal_jacobian (F (p,q))=
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (exterior_product (projection_normal_vector p) (projection_normal_vector q)).
Proof.
move=> hF p q.
rewrite (@euclidean_normal_jacobian_unit_value R n (a+r) (F (p,q))
  (@top_vector R (a+r) (R_n R (a+r)) (@coordinate_basis R (a+r)))
  (@euclidean_coordinate_top_vector_unit R (a+r))).
by rewrite (@stacked_normal_top_product R n a r F hF p q).
Qed.
