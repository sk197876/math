(** Federer (1969), 3.2.28(2), printed p. 264:
    an isometry on the orthogonal complement of the kernel
    has top nonzero exterior norm one. This supporting
    intrinsic proof uses the projection and exterior isometry
    laws of 1.7.7, p. 34, including zero quotient dimension. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP InnerProductUP InnerNorm OrthogonalMaps AdjointUP AdjointCriteria
  GramSchmidt OrthonormalFamilies OrthonormalisationUP LinearBasis
  ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorNorm ExteriorProjectionNorm
  InnerExterior InnerExteriorPositivity FiniteExteriorPowers OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_quotient_top_exterior_norm_one]:
    JQ=1 in Federer 3.2.28(2), p. 264, from
    the proved horizontal isometry and orthogonal kernel.
    Supporting general linear result: an orthogonal projection
    onto an r-dimensional space followed by an isometry has
    r-th exterior operator norm one, by 1.7.7, p. 34. *)
Theorem orthogonal_quotient_top_exterior_norm_one (R:realType)
    (h2:(1+1:R)!=0) (U V W:lmodType R)
    (BU:U->U->R) (BV:V->V->R) (BW:W->W->R)
    (hU:is_inner_product BU) (hV:is_inner_product BV) (hW:is_inner_product BW)
    r (b:'I_r->U) (hb:is_basis b)
    (H:{linear U->V}) (P:{linear V->U}) (A:{linear U->W}):
  is_orthogonal_map BU BV H ->is_adjoint BU BV H P ->
  is_orthogonal_map BU BW A ->
  is_operator_norm (exterior_inner_productP h2 hV r)
    (exterior_inner_productP h2 hW r)
    (exterior_power_map (linear_comp A P) r) 1.
Proof.
move=>hH hP hA.
have hProj:is_orthogonal_projection BV BU P by exists H.
have hCancel:cancel H P:=(orthogonal_iff_adjoint_left_inverse hU hP).1 hH.
have [e [he hGS]]:=orthonormal_basis_exists hU hb.
have hE:=orthonormalisation_orthonormal hGS.
pose z:=e_lambda e (ord_tuple r).
have hZ:exterior_norm h2 hU z= 1:=orthonormal_product_unit_norm h2 hU hE.
constructor.
- move=>x hx.
  change (exterior_norm h2 hW (exterior_power_map (linear_comp A P) r x)<=1).
  rewrite -exterior_power_map_composition.
  rewrite (exterior_orthogonal_norm h2 hU hW hA).
  exact:le_trans (exterior_projection_norm_bound h2 hV hU hProj x) hx.
- exists (exterior_power_map H r z); split.
  + change (exterior_norm h2 hV (exterior_power_map H r z)<=1).
    by rewrite (exterior_orthogonal_norm h2 hU hV hH) hZ.
  + change (exterior_norm h2 hW (exterior_power_map (linear_comp A P) r
      (exterior_power_map H r z))= 1).
    rewrite -exterior_power_map_composition.
    rewrite (exterior_adjoint_retraction hU hP hH).
    by rewrite (exterior_orthogonal_norm h2 hU hW hA) hZ.
Qed.
