(** Federer (1969), 1.7.6–1.7.7, pp. 33–34:
    a scaled orthogonal quotient has exterior norm equal
    to the scale raised to its quotient dimension.
    Supporting Jr Phi=2^(-r/2) in 3.2.47, p. 283. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP InnerProductUP InnerNorm OrthogonalMaps AdjointUP
  LinearBasis OrthogonalQuotientExteriorNorm InnerExteriorPositivity
  ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorNorm OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scaled_orthogonal_quotient_top_exterior_norm]:
    the exact horizontal scale gives its r-th power
    for the r-Jacobian in 3.2.47, p. 283,
    by 1.7.6–1.7.7, pp. 33–34. Dimension
    zero and zero scale are retained. All quotient,
    adjoint and isometry laws are genuine obligations. *)
Theorem scaled_orthogonal_quotient_top_exterior_norm (R:realType)
    (h2:(1+1:R)!=0) (U V W:lmodType R)
    BU BV BW (hU:@is_inner_product R U BU)
    (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    r (b:'I_r->U) (hb:is_basis b)
    (H:{linear U->V}) (P:{linear V->U}) (A:{linear U->W}) (F:{linear V->W}) c:
  is_orthogonal_map BU BV H ->is_adjoint BU BV H P ->
  is_orthogonal_map BU BW A ->0<=c ->
  (forall x,F x=c*:A (P x)) ->
  is_operator_norm (exterior_inner_productP h2 hV r)
    (exterior_inner_productP h2 hW r) (exterior_power_map F r) (c^+r).
Proof.
move=>hH hP hA hc hF.
have hOne:=@orthogonal_quotient_top_exterior_norm_one R h2 U V W BU BV BW hU hV hW r b hb H P A hH hP hA.
have hScale x:exterior_power_map F r x=c^+r*:exterior_power_map (linear_comp A P) r x.
  exact (@exterior_power_map_scale R V W (linear_comp A P) F c hF r x).
have hPower:0<=c^+r by apply:exprn_ge0.
constructor.
- move=>x hx; rewrite hScale inner_normZ (ger0_norm hPower).
  have hBound:=@operator_norm_unit_bound R _ _ _ _
    (exterior_inner_productP h2 hV r) (exterior_inner_productP h2 hW r)
    (exterior_power_map (linear_comp A P) r) 1 hOne x hx.
  have h:=ler_wpM2l hPower hBound.
  by rewrite mulr1 in h.
- have [x [hx hValue]]:=operator_norm_attained hOne.
  exists x; split; first exact hx.
  by rewrite hScale inner_normZ (ger0_norm hPower) hValue mulr1.
Qed.
