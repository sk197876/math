(** Federer (1969), 1.7.6, p. 34: the diagonal
    squared-norm calculation for orthogonal exterior images.
    Supporting the small exterior norm in 3.2.31, p. 269. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerNorm InnerExterior InnerExteriorProducts InnerExteriorPositivity
  ExteriorNorm ExteriorMaps ExteriorGrading FiniteExteriorPowers ExteriorIndices
  LinearBasis FiniteDualDimension OrthonormalFamilies OrthonormalBilinearCoordinates OrthogonalExteriorImages
  ExteriorBasisWedgeNorm ExteriorOperatorEstimate ExteriorOperatorNorm OperatorNormUP OperatorNormLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_exterior_basis_vector_bound]: the
    diagonal squared-norm argument in Federer 1.7.6, p. 34,
    supporting the approximation of a rank-deficient symmetric
    map in 3.2.31, p. 269. A common bound on actual images
    of the orthonormal exterior basis controls every exterior
    vector. The coefficient need not be a power of an ordinary
    operator norm. Zero coefficients and degrees are retained. *)
Theorem orthogonal_exterior_basis_vector_bound (R:realType)
    (h2:(1+1:R)!=0) (V U:lmodType R) (B:V->V->R) (C:U->U->R)
    (hB:is_inner_product B) (hC:is_inner_product C) n
    (e:'I_n->V) (he:is_basis e) (hE:orthonormal_family B e)
    (f:{linear V->U}) k (a:R):
  0<=a ->(forall i j,i!=j ->C (f (e i)) (f (e j))=0) ->
  (forall lambda:Lambda n k,
    exterior_norm h2 hC (e_lambda (fun i=>f (e i)) (val lambda))<=a) ->
  forall x:exterior_power V k,
    exterior_norm h2 hC (exterior_power_map f k x)<=a*exterior_norm h2 hB x.
Proof.
move=>ha hOrth hWords x.
have hbe:=@finite_e_lambda_basis R n V e he h2 k.
have hExpansion:=@orthonormal_basis_vector_expansion R (exterior_power V k)
  (Finite.clone (Lambda n k) _) (fun lambda=>e_lambda e (val lambda)) hbe x.
pose c:=fun lambda=>dual_basis hbe lambda x.
have hPos:0<=a*exterior_norm h2 hB x:=mulr_ge0 ha (exterior_norm_nonnegative h2 hB x).
rewrite -(ler_sqr (exterior_norm_nonnegative h2 hC _) hPos) exprMn.
rewrite {1}hExpansion linear_sum.
under eq_bigr do rewrite linearZ exterior_map_indexed_product.
rewrite exterior_norm_square (@orthogonal_bilinear_diagonal_sum R (exterior_power U k)
  (@exterior_inner_form R h2 U C hC k) (exterior_inner_form_bilinear h2 hC k)
  (Finite.clone (Lambda n k) _) (fun lambda=>e_lambda (fun i=>f (e i)) (val lambda))
  (@orthogonal_exterior_index_family R h2 U C hC n (fun i=>f (e i)) hOrth k) c).
have hNorm:exterior_norm h2 hB x^+2=\sum_lambda (c lambda)^+2.
  rewrite hExpansion; exact (@exterior_basis_expansion_norm_square R h2 V B hB n e hE k c).
rewrite hNorm mulr_sumr; apply:ler_sum=>lambda _.
rewrite -exterior_norm_square mulrC.
apply:(ler_wpM2r (sqr_ge0 (c lambda))).
rewrite (ler_sqr (exterior_norm_nonnegative h2 hC _) ha).
exact (hWords lambda).
Qed.

(** Source for [orthogonal_exterior_basis_operator_bound]: the
    operator-norm consequence of the diagonal calculation in
    Federer 1.7.6, p. 34, supporting the small-exterior
    automorphism of 3.2.31, p. 269. All basis image bounds
    concern the actual map; no Jacobian estimate is assumed. *)
Theorem orthogonal_exterior_basis_operator_bound (R:realType)
    (h2:(1+1:R)!=0) (V U:lmodType R) (B:V->V->R) (C:U->U->R)
    (hB:is_inner_product B) (hC:is_inner_product C) n
    (e:'I_n->V) (he:is_basis e) (hE:orthonormal_family B e)
    (f:{linear V->U}) k (a:R):
  0<=a ->(forall i j,i!=j ->C (f (e i)) (f (e j))=0) ->
  (forall lambda:Lambda n k,
    exterior_norm h2 hC (e_lambda (fun i=>f (e i)) (val lambda))<=a) ->
  exterior_operator_norm h2 hB hC he f k<=a.
Proof.
move=>ha hOrth hWords.
apply:(operator_norm_le_unit (exterior_operator_normP h2 hB hC he f k) a).2=>x hx.
have hh:=@orthogonal_exterior_basis_vector_bound R h2 V U B C hB hC n e he hE f k a
  ha hOrth hWords x.
apply:(le_trans hh).
have hBound:=ler_wpM2l ha hx.
by rewrite mulr1 in hBound.
Qed.
