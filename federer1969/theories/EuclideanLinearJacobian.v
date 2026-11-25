(** Federer (1969), 3.2.1, p. 241: the k-dimensional
    Jacobian uses the norm of the kth exterior power from
    1.7.6, pp. 33–34. This interface uses its existing opaque
    norm and exterior-algebra specifications, including degree zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanLinearMaps InnerNorm InnerProductUP InnerExterior InnerExteriorPositivity ExteriorGrading ExteriorMaps
  ExteriorNorm ExteriorOperatorNorm OperatorNormUP OperatorNorm TopExteriorNorm TopExteriorInjectivity
  Adjoint AdjointUP EuclideanNormalJacobian FiniteExteriorPowers OrthonormalFamilies ExteriorOperatorEstimate.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_linear_jacobian]: the numerical operator
    in the two definitions of Federer 3.2.1, p. 241: take the
    norm of the kth induced exterior map. The degree k is any
    natural number, with no restriction by source or target dimension. *)
Definition euclidean_linear_jacobian (R:realType) m n k (L:Hom (R_n R m) (R_n R n)):R :=
  exterior_operator_norm (euclidean_two_nonzero R)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (@coordinate_basisP R m) (hom_as_linear L) k.

(** Source for [euclidean_linear_jacobian_nonnegative]: the norm
    in Federer 3.2.1, p. 241, is nonnegative by 1.7.6, p. 33.
    Supporting consequence, retaining all dimensions and degrees. *)
Lemma euclidean_linear_jacobian_nonnegative (R:realType) m n k (L:Hom (R_n R m) (R_n R n)) :
  0<=euclidean_linear_jacobian k L.
Proof. exact (operator_norm_nonnegative (exterior_operator_normP _ _ _ _ _ _)). Qed.

(** Source for [euclidean_linear_jacobian_bound]: the upper bound
    inherited from 1.7.6, pp. 33–34, for the Jacobian defined
    in Federer 3.2.1, p. 241. Supporting lemma: J_k L<=||L||^k. *)
Lemma euclidean_linear_jacobian_bound (R:realType) m n k (L:Hom (R_n R m) (R_n R n)) :
  euclidean_linear_jacobian k L<=
    (linear_operator_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
      (@coordinate_basisP R m) (hom_as_linear L))^+k.
Proof. exact (exterior_operator_norm_bound _ _ _ _ _ _). Qed.

(** Source for [euclidean_linear_jacobian_top_positive]: injectivity
    is equivalent to positivity of the top-source Jacobian in
    Federer 3.2.1, p. 241, by the recalled 1.7.6, p. 34.
    This supports the decomposition in 3.2.2, p. 242. *)
Lemma euclidean_linear_jacobian_top_positive (R:realType) m n (L:Hom (R_n R m) (R_n R n)) :
  0<euclidean_linear_jacobian m L <-> injective L.
Proof. exact (top_exterior_norm_positive_iff_injective _ _ _ _ _). Qed.

(** Source for [euclidean_linear_jacobian_determinant]: the top
    square Jacobian of Federer 3.2.1, p. 241, equals the absolute
    determinant by 1.7.6, p. 33. Supporting specialization for
    the linear changes of variables in the subsequent area proof. *)
Lemma euclidean_linear_jacobian_determinant (R:realType) m (L:Hom (R_n R m) (R_n R m)) :
  euclidean_linear_jacobian m L=`|euclidean_det (hom_as_linear L)|.
Proof. exact (top_exterior_operator_determinant _ _ _ _). Qed.

(** Source for [euclidean_linear_jacobian_normal]: the target-degree
    Jacobian in Federer 3.2.1, p. 241, agrees with the normal
    Jacobian already used for 2.10.16, p. 178. This follows
    from exterior-adjoint norm equality in 1.7.6, p. 33. *)
Lemma euclidean_linear_jacobian_normal (R:realType) m n (L:Hom (R_n R m) (R_n R n)) :
  euclidean_linear_jacobian n L=euclidean_normal_jacobian (hom_as_linear L).
Proof.
exact (@exterior_operator_adjoint_norm_equal R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m n
  (@coordinate_basis R m) (@coordinate_basis R n) (@coordinate_basisP R m) (@coordinate_basisP R n)
  (hom_as_linear L) (inner_adjoint (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (@coordinate_basisP R m) (hom_as_linear L))
  (inner_adjointP (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) (@coordinate_basisP R m) (hom_as_linear L)) n).
Qed.

(** Source for [euclidean_linear_jacobian_zero_degree]: degree zero
    in Federer 3.2.1, p. 241, using the empty exterior product
    of 1.3.1 and its unit norm in 1.7.5, p. 32. Every linear
    map has J_0=1, even when an ambient dimension is zero. *)
Lemma euclidean_linear_jacobian_zero_degree (R:realType) m n (L:Hom (R_n R m) (R_n R n)) :
  euclidean_linear_jacobian 0 L= 1.
Proof.
have hEmpty (V:lmodType R) (B:V->V->R) (e:'I_0->V):orthonormal_family B e.
  move=>i; by have:=ltn_ord i; rewrite ltn0.
pose e:=fun _:'I_0=>(0:R_n R m).
pose w:=e_lambda e (ord_tuple 0).
have hSource:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) w= 1.
  exact (orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m)
    (hEmpty _ _ e)).
have hTarget:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (exterior_power_map (hom_as_linear L) 0 w)= 1.
  rewrite /w exterior_map_indexed_product.
  exact (orthonormal_product_unit_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (hEmpty _ _ (fun i=>L (e i)))).
apply/eqP; rewrite eq_le; apply/andP; split.
- have hb:=euclidean_linear_jacobian_bound 0 L; by rewrite expr0 in hb.
- have hb:=@operator_norm_unit_bound R (exterior_power (R_n R m) 0) (exterior_power (R_n R n) 0)
    (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R m) (@euclidean_inner_product R m) (@euclidean_inner_productP R m) 0)
    (@exterior_inner_form R (euclidean_two_nonzero R) (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) 0)
    (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R m) (@euclidean_inner_product R m) (@euclidean_inner_productP R m) 0)
    (@exterior_inner_productP R (euclidean_two_nonzero R) (R_n R n) (@euclidean_inner_product R n) (@euclidean_inner_productP R n) 0)
    (exterior_power_map (hom_as_linear L) 0) (euclidean_linear_jacobian 0 L)
    (exterior_operator_normP (euclidean_two_nonzero R) (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
      (@coordinate_basisP R m) (hom_as_linear L) 0) w.
  have hw:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) w<=1 by rewrite hSource.
  have hh:=hb hw.
  change (is_true (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
    (exterior_power_map (hom_as_linear L) 0 w)<=euclidean_linear_jacobian 0 L)) in hh.
  by rewrite hTarget in hh.
Qed.
