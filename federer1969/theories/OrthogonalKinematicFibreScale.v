(** Federer (1969), 3.2.48, p. 284: the actual
    fibre graph magnifies every Hilbert Hom distance by sqrt(2).
    This establishes the precise metric factor before transporting
    any Hausdorff measures or signed integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets ring.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric OrthogonalMaps EuclideanHomInnerCharts
  EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  SphericalOrthogonalFibreIsometry ProductInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_kinematic_fibre_distance]: the
    printed sqrt(2) distance factor of x to (x,g inverse x),
    3.2.48, p. 284. It holds on the full ambient
    Hom space, including dimension zero and arbitrary original subsets. *)
Theorem orthogonal_kinematic_fibre_distance (R:realType) N
    (g x y:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  inner_norm (product_inner_productP
    (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N))
    ((x,hom_comp (euclidean_rectangular_adjoint g) x)-
      (y,hom_comp (euclidean_rectangular_adjoint g) y))=
  Num.sqrt (2:R)*inner_norm (@euclidean_hom_inner_productP R N N) (x-y).
Proof.
move=>hg.
pose hH:=@euclidean_hom_inner_productP R N N.
have hDistance:=@euclidean_orthogonal_left_translation_distance R N
  (euclidean_rectangular_adjoint g) x y (@euclidean_orthogonal_adjoint_orthogonal R N g hg).
apply:inner_norm_value.
- exact (mulr_ge0 (sqrtr_ge0 _) (inner_norm_nonnegative hH _)).
- rewrite exprMn sqr_sqrtr ?ler0n //.
  change (2*(inner_norm hH (x-y))^+2=
    product_inner hH hH (x-y,hom_comp (euclidean_rectangular_adjoint g) x-
      hom_comp (euclidean_rectangular_adjoint g) y)
      (x-y,hom_comp (euclidean_rectangular_adjoint g) x-
        hom_comp (euclidean_rectangular_adjoint g) y)).
  rewrite product_innerE -!inner_norm_sqr hDistance; ring.
Qed.
