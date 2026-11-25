(** Federer (1969), 1.7.6, pp. 33-34: the pointwise exterior-power norm
    estimate. The proof follows the book's orthogonal-image basis and
    diagonal squared-norm expansion. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization InnerExterior
  InnerExteriorPositivity InnerExteriorBasis ExteriorNorm ExteriorHadamardBound
  OrthogonalExteriorImages OperatorNormUP OrthogonalImageBasis LinearBasis FiniteDualDimension Hom ExteriorIndices
  OrthonormalFamilies OrthonormalBilinearCoordinates FiniteExteriorPowers
  ExteriorGrading ExteriorMaps ExteriorAlgebra AlgebraUP GradedComponents
  ExteriorBasisWedgeNorm SimpleAdaptedBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_map_indexed_product]: Federer 1.7.6,
    p. 34, the image of a basis product is the product of its
    images, an instance of the exterior functor from 1.3.1. *)
Lemma exterior_map_indexed_product (R : fieldType) (V U : lmodType R)
    (f : {linear V -> U}) (I : choiceType) (e : I -> V) m (t : m.-tuple I) :
  exterior_power_map f m (e_lambda e t) = e_lambda (fun i => f (e i)) t.
Proof.
apply: val_inj; change (exterior_algebra_map f (component_val (e_lambda e t)) =
  component_val (e_lambda (fun i => f (e i)) t)).
by rewrite !e_lambdaE exterior_algebra_map_word -map_comp.
Qed.

(** Source for [exterior_map_unit_product_bound]: Federer
    1.7.6, p. 34, each image basis product has norm at most
    the operator norm raised to its degree. The product bound
    from 1.7.5 includes singular and empty-product cases. *)
Lemma exterior_map_unit_product_bound (R : rcfType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) L (hL : is_operator_norm hB hC f L)
    n (e : 'I_n -> V) (ho : orthonormal_family B e)
    m (lambda : Lambda n m) :
  exterior_norm h2 hC (e_lambda (fun i => f (e i)) (val lambda)) <= L^+m.
Proof.
rewrite indexed_productE.
apply: le_trans (exterior_product_norm_bound h2 hC _) _.
have he : (\prod_(i : 'I_m) L) = L^+m by rewrite prodr_const card_ord.
rewrite -he; apply: ler_prod => i _; apply/andP; split.
- exact: inner_norm_nonnegative.
- apply: (@operator_norm_unit_bound R V U B C hB hC f L hL).
  by rewrite (@orthonormal_norm1 R V B hB (Finite.clone 'I_n _) e ho).
Qed.

(** Source for [exterior_operator_pointwise_bound]: Federer
    1.7.6, p. 34, displayed diagonal estimate and its square
    root: |(exterior_m f)(xi)| <= ||f||^m |xi|. Only the source
    requires a finite basis; the target may have arbitrary dimension. *)
Theorem exterior_operator_pointwise_bound (R : realType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (b : 'I_n -> V) (hb : is_basis b)
    (f : {linear V -> U}) L (hL : is_operator_norm hB hC f L)
    m (x : exterior_power V m) :
  exterior_norm h2 hC (exterior_power_map f m x) <= L^+m * exterior_norm h2 hB x.
Proof.
have [e [he [ho hf]]] := orthonormal_orthogonal_image_basis hB hC f hb.
have hbe := @finite_e_lambda_basis R n V e he h2 m.
have hex := @orthonormal_basis_vector_expansion R (exterior_power V m)
  (Finite.clone (Lambda n m) _) (fun lambda => e_lambda e (val lambda)) hbe x.
pose c := fun lambda => dual_basis hbe lambda x.
have hm : 0 <= L^+m := exprn_ge0 _ (operator_norm_nonnegative hL).
have hp : 0 <= L^+m * exterior_norm h2 hB x := mulr_ge0 hm (exterior_norm_nonnegative h2 hB x).
rewrite -(ler_sqr (exterior_norm_nonnegative h2 hC _) hp) exprMn.
rewrite {1}hex linear_sum.
under eq_bigr do rewrite linearZ exterior_map_indexed_product.
rewrite exterior_norm_square (@orthogonal_bilinear_diagonal_sum R (exterior_power U m)
  (@exterior_inner_form R h2 U C hC m) (exterior_inner_form_bilinear h2 hC m)
  (Finite.clone (Lambda n m) _) (fun lambda => e_lambda (fun i => f (e i)) (val lambda))
  (@orthogonal_exterior_index_family R h2 U C hC n (fun i => f (e i)) hf m) c).
have hx : exterior_norm h2 hB x ^+2 = \sum_lambda (c lambda)^+2.
  rewrite hex; exact (@exterior_basis_expansion_norm_square R h2 V B hB n e ho m c).
rewrite hx mulr_sumr; apply: ler_sum => lambda _.
rewrite -exterior_norm_square mulrC.
apply: ler_wpM2r; first exact: sqr_ge0.
rewrite (ler_sqr (exterior_norm_nonnegative h2 hC _) hm).
exact (@exterior_map_unit_product_bound R h2 V U B C hB hC f L hL n e ho m lambda).
Qed.
