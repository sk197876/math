(** Federer (1969), 3.2.28, pp. 265–267:
    viewing the tangent image inside its ambient
    inner-product space does not change the exterior
    operator norm, by 1.7.5, p. 32. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP InnerProductUP InnerNorm OrthogonalMaps ExteriorGrading
  ExteriorMaps ExteriorMapScaling ExteriorNorm ExteriorNormNaturality InnerExteriorPositivity OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [exterior_isometric_postcomposition_norm]:
    a tangent-target inclusion preserves the computed
    exterior Jacobian in Federer 3.2.28, pp. 265–267.
    The same unit-ball bound and attainment prove the
    value, so no finite-dimensional norm construction
    or new selected supremum is needed. *)
Theorem exterior_isometric_postcomposition_norm (R:realType) (h2:(1+1:R)!=0)
    (U V W:lmodType R) (B:U->U->R) (C:V->V->R) (D:W->W->R)
    (hB:is_inner_product B) (hC:is_inner_product C) (hD:is_inner_product D)
    (f:{linear U->V}) (t:{linear V->W}) (g:{linear U->W}) q j:
  is_orthogonal_map C D t ->(forall u,g u=t (f u)) ->
  is_operator_norm (exterior_inner_productP h2 hB q) (exterior_inner_productP h2 hC q)
    (exterior_power_map f q) j ->
  is_operator_norm (exterior_inner_productP h2 hB q) (exterior_inner_productP h2 hD q)
    (exterior_power_map g q) j.
Proof.
move=>hT hEq hNorm.
have hG:g =1 linear_comp t f by move=>u; exact:hEq.
have hValue x:exterior_norm h2 hD (exterior_power_map g q x)=
    exterior_norm h2 hC (exterior_power_map f q x).
  rewrite (@exterior_power_map_ext R U W g (linear_comp t f) hG q x)
    -exterior_power_map_composition.
  exact:(@exterior_norm_orthogonal_natural R h2 V W C D hC hD t hT q
    (exterior_power_map f q x)).
constructor.
- move=>x hx; change (exterior_norm h2 hD (exterior_power_map g q x)<=j).
  rewrite hValue; exact:(@operator_norm_unit_bound R _ _ _ _ _ _ _ j hNorm x hx).
- have [x [hx hVal]]:=operator_norm_attained hNorm.
  exists x; split; first exact hx.
  change (exterior_norm h2 hD (exterior_power_map g q x)=j).
  by rewrite hValue.
Qed.
