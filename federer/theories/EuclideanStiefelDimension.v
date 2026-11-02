(** Federer (1969), 3.2.28(1), printed p. 263:
    the two displayed expressions for the Stiefel dimension.
    Natural subtraction is used only with its stated truncation;
    the equality also holds at zero dimensions. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  OrthogonalMaps EuclideanHomInnerCharts FiniteInnerSubmanifoldUP
  EuclideanStiefelSubmanifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope nat_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_stiefel_dimension_identity]:
    mn-m(m+1)/2=m(2n-m-1)/2, Federer
    3.2.28(1), p. 263. Consecutive integers
    have even product, so division introduces no rounding error. *)
Lemma euclidean_stiefel_dimension_identity m n:
  m*(2*n-m-1)%/2=m*n-m*(m+1)%/2.
Proof.
have hEven:2%|m*(m+1).
  by rewrite dvdn2 oddM addn1 oddS andbN.
have hMul:m*(2*n)=(m*n)*2 by rewrite mulnA mulnAC.
have hPolynomial:m*(2*n-m-1)=(m*n)*2-m*(m+1).
  rewrite !mulnBr muln1 hMul -subnDA.
  by rewrite mulnDr muln1.
by rewrite hPolynomial (@divnBr ((m*n)*2) (m*(m+1)) 2 hEven) mulnK.
Qed.

(** Source for [euclidean_stiefel_submanifold_printed_dimension]:
    the full manifold assertion and printed dimension in
    Federer 3.2.28(1), p. 263. Each finite positive
    class is supplied, hence class infinity; the book's m<=n
    range is retained, including its zero-dimensional extensions. *)
Theorem euclidean_stiefel_submanifold_printed_dimension (R:realType) m n k:
  (m<=n)%N ->(1<=k)%N ->
  is_inner_submanifold (@euclidean_hom_inner_product R m n)
    (m*(2*n-m-1)%/2)%N k
    [set g:Hom (R_n R m) (R_n R n)|
      is_orthogonal_map (@euclidean_inner_product R m)
        (@euclidean_inner_product R n) (hom_as_linear g)].
Proof.
move=>hmn hk; rewrite euclidean_stiefel_dimension_identity.
exact:euclidean_stiefel_submanifold.
Qed.
