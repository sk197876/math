(** Federer (1969), 3.2.2, p. 242: the pointwise differential
    sandwich implies the top-source Jacobian sandwich. The proof
    expands 1.7.6 on an orthonormal basis with orthogonal images. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerNorm InnerNormalization OrthonormalFamilies OrthogonalImageBasis ExteriorGrading ExteriorNorm
  InnerExterior InnerExteriorPositivity InnerExteriorTriangular ExteriorHadamardEquality FiniteExteriorPowers
  ExteriorOperatorNorm ExteriorOperatorEstimate TopExteriorNorm EuclideanLinearMaps EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_top_jacobian_sandwich]: the assertion
    that bounds on all vector lengths imply bounds on J_m,
    Federer 3.2.2, p. 242. Diagonalize the squared image norm
    by the proved orthogonal-image-basis theorem, then multiply
    its m scalar inequalities. Includes m=0 and singular maps. *)
Theorem euclidean_top_jacobian_sandwich (R:realType) m n
    (L:Hom (R_n R m) (R_n R n)) c C :
  0<=c -> 0<=C ->
  (forall v,c*inner_norm (@euclidean_inner_productP R m) v<=inner_norm (@euclidean_inner_productP R n) (L v)) ->
  (forall v,inner_norm (@euclidean_inner_productP R n) (L v)<=C*inner_norm (@euclidean_inner_productP R m) v) ->
  c^+m<=euclidean_linear_jacobian m L /\ euclidean_linear_jacobian m L<=C^+m.
Proof.
move=>hc hC hLower hUpper.
have [e [he [ho hImages]]]:=@orthonormal_orthogonal_image_basis R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  (hom_as_linear L) m (@coordinate_basis R m) (@coordinate_basisP R m).
pose w:=e_lambda e (ord_tuple m).
have hw:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) w= 1.
  exact (orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) ho).
have hJ:euclidean_linear_jacobian m L=\prod_i inner_norm (@euclidean_inner_productP R n) (L (e i)).
  rewrite /euclidean_linear_jacobian (@top_exterior_operator_unit_value R (euclidean_two_nonzero R)
    (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m
    (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear L) w hw).
  rewrite /w exterior_map_indexed_product.
  exact (orthogonal_product_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n) hImages).
rewrite hJ.
have hLen i:inner_norm (@euclidean_inner_productP R m) (e i)= 1:=orthonormal_norm1 (@euclidean_inner_productP R m) ho i.
have hl i:c<=inner_norm (@euclidean_inner_productP R n) (L (e i)).
  by have hh:=hLower (e i); rewrite hLen mulr1 in hh.
have hu i:inner_norm (@euclidean_inner_productP R n) (L (e i))<=C.
  by have hh:=hUpper (e i); rewrite hLen mulr1 in hh.
have hec:(\prod_(i:'I_m) c)=c^+m by rewrite prodr_const card_ord.
have heC:(\prod_(i:'I_m) C)=C^+m by rewrite prodr_const card_ord.
split.
- rewrite -hec; apply:ler_prod=>i _; apply/andP; by split.
- rewrite -heC; apply:ler_prod=>i _; apply/andP; split; [exact:inner_norm_nonnegative|exact:hu].
Qed.
