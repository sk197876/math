(** Federer (1969), 3.2.22, pp. 258–259: supporting
    comparison of the approximate exterior Jacobian in coordinates.
    For an induced exterior map it suffices to bound unit simple
    words. The proof expands the orthogonal image basis of 1.7.6. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerNorm InnerNormalization InnerExterior InnerExteriorPositivity
  InnerExteriorBasis InnerExteriorTriangular ExteriorNorm ExteriorMaps ExteriorGrading
  FiniteExteriorPowers ExteriorIndices LinearBasis FiniteDualDimension FiniteOrdinalBasis
  OrthonormalBilinearCoordinates OrthogonalExteriorImages ExteriorBasisWedgeNorm
  OrthonormalFamilies OrthogonalImageBasis SimpleAdaptedBasis ExteriorOperatorEstimate
  ExteriorOperatorNorm OperatorNormUP OperatorNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_unit_word_bound_pointwise]: supporting
    linear exterior-norm comparison in Federer 3.2.22,
    p. 259, using 1.7.6, pp. 33–34.
    An orthonormal source basis with orthogonal images has
    mutually orthogonal exterior image words. Bounding each
    word therefore bounds every exterior vector, in every degree. *)
Theorem exterior_unit_word_bound_pointwise (R:realType)
    (h2:(1+1:R)!=0) (V U:lmodType R) (B:V->V->R) (C:U->U->R)
    (hB:is_inner_product B) (hC:is_inner_product C)
    n (b:'I_n->V) (hb:is_basis b) (f:{linear V->U}) q (J:R):
  0<=J ->
  (forall v:'I_q->V,exterior_norm h2 hB (e_lambda v (ord_tuple q))<=1 ->
    exterior_norm h2 hC (e_lambda (fun i=>f (v i)) (ord_tuple q))<=J) ->
  forall x:exterior_power V q,
    exterior_norm h2 hC (exterior_power_map f q x)<=J*exterior_norm h2 hB x.
Proof.
move=>hJ hWord x.
have [e [he [ho hf]]]:=orthonormal_orthogonal_image_basis hB hC f hb.
have hbe:=@finite_e_lambda_basis R n V e he h2 q.
have hex:=@orthonormal_basis_vector_expansion R (exterior_power V q)
  (Finite.clone (Lambda n q) _) (fun lambda=>e_lambda e (val lambda)) hbe x.
pose c:=fun lambda=>dual_basis hbe lambda x.
have hp:0<=J*exterior_norm h2 hB x:=mulr_ge0 hJ (exterior_norm_nonnegative h2 hB x).
rewrite -(ler_sqr (exterior_norm_nonnegative h2 hC _) hp) exprMn.
rewrite {1}hex linear_sum.
under eq_bigr do rewrite linearZ exterior_map_indexed_product.
rewrite exterior_norm_square (@orthogonal_bilinear_diagonal_sum R (exterior_power U q)
  (@exterior_inner_form R h2 U C hC q) (exterior_inner_form_bilinear h2 hC q)
  (Finite.clone (Lambda n q) _) (fun lambda=>e_lambda (fun i=>f (e i)) (val lambda))
  (@orthogonal_exterior_index_family R h2 U C hC n (fun i=>f (e i)) hf q) c).
have hx:exterior_norm h2 hB x^+2=\sum_lambda (c lambda)^+2.
  rewrite hex; exact (@exterior_basis_expansion_norm_square R h2 V B hB n e ho q c).
rewrite hx mulr_sumr; apply:ler_sum=>lambda _.
rewrite -exterior_norm_square mulrC.
apply:ler_wpM2r; first exact:sqr_ge0.
rewrite (ler_sqr (exterior_norm_nonnegative h2 hC _) hJ).
have hUnit:exterior_norm h2 hB (e_lambda e (val lambda))= 1.
  exact (@orthonormal_norm1 R (exterior_power V q) (@exterior_inner_form R h2 V B hB q)
    (@exterior_inner_productP R h2 V B hB q) (Finite.clone (Lambda n q) _)
    (fun lambda=>e_lambda e (val lambda)) (@exterior_orthonormal_family R h2 V B hB n e ho q) lambda).
rewrite indexed_productE; apply:hWord.
by rewrite -indexed_productE hUnit.
Qed.

(** Source for [exterior_unit_word_operator_bound]: the least
    operator bound used in Federer 3.2.22, p. 259,
    is determined by its bounds on unit exterior words.
    No extra simple-maximizer or attainment premise is assumed. *)
Theorem exterior_unit_word_operator_bound (R:realType)
    (h2:(1+1:R)!=0) (V U:lmodType R) (B:V->V->R) (C:U->U->R)
    (hB:is_inner_product B) (hC:is_inner_product C)
    n (b:'I_n->V) (hb:is_basis b) (f:{linear V->U}) q (J:R):
  0<=J ->
  (forall v:'I_q->V,exterior_norm h2 hB (e_lambda v (ord_tuple q))<=1 ->
    exterior_norm h2 hC (e_lambda (fun i=>f (v i)) (ord_tuple q))<=J) ->
  exterior_operator_norm h2 hB hC hb f q<=J.
Proof.
move=>hJ hWord; apply:(operator_norm_le_unit (exterior_operator_normP h2 hB hC hb f q) J).2=>x hx.
have h:=exterior_unit_word_bound_pointwise hb hJ hWord x.
apply:(le_trans h _); apply:(le_trans (ler_wpM2l hJ hx) _); by rewrite mulr1.
Qed.
