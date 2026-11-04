(** Federer (1969), 3.2.48, p. 285: the vertical
    arrows of the differential diagram are actual source
    isometries. Supporting invariance of each exterior operator
    norm under a bijective source isometry, by 1.7.6,
    pp. 33–34, through its bound and attainment laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import TensorUP InnerProductUP InnerNorm OrthogonalMaps
  ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorNorm ExteriorNormNaturality
  InnerExteriorPositivity OperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [exterior_isometric_precomposition_norm]: supporting
    the source isometries in the actual commutative diagram
    of 3.2.48, p. 285. Both inverse laws,
    preservation of the specified inner product and actual
    commutation with the two maps are proved obligations.
    All natural exterior degrees, including zero, remain. *)
Theorem exterior_isometric_precomposition_norm (R:realType) (h2:(1+1:R)!=0)
    (U V W:lmodType R) B C D (hB:@is_inner_product R U B)
    (hC:@is_inner_product R V C) (hD:@is_inner_product R W D)
    (i:{linear U->V}) (j:{linear V->U}) (f:{linear U->W}) (g:{linear V->W}) q L:
  cancel i j ->cancel j i ->is_orthogonal_map B C i ->
  (forall x,g (i x)=f x) ->
  is_operator_norm (exterior_inner_productP h2 hB q) (exterior_inner_productP h2 hD q)
    (exterior_power_map f q) L ->
  is_operator_norm (exterior_inner_productP h2 hC q) (exterior_inner_productP h2 hD q)
    (exterior_power_map g q) L.
Proof.
move=>hLeft hRight hI hCommute hNorm.
have hJ:is_orthogonal_map C B j.
  move=>x y; by rewrite -(hI (j x) (j y)) !hRight.
have hG:g=1 linear_comp f j.
  move=>x; change (g x=f (j x)).
  by rewrite -hCommute hRight.
have hF:linear_comp g i=1 f by move=>x; exact (hCommute x).
have hImage x:exterior_power_map g q x=exterior_power_map f q (exterior_power_map j q x).
  rewrite (@exterior_power_map_ext R V W g (linear_comp f j) hG q x).
  exact (esym (@exterior_power_map_composition R V U W j f q x)).
have hForward x:exterior_power_map g q (exterior_power_map i q x)=exterior_power_map f q x.
  rewrite exterior_power_map_composition.
  exact (@exterior_power_map_ext R U W (linear_comp g i) f hF q x).
constructor.
- move=>x hx; change (exterior_norm h2 hD (exterior_power_map g q x)<=L).
  rewrite hImage; apply:(operator_norm_unit_bound hNorm).
  change (exterior_norm h2 hB (exterior_power_map j q x)<=1).
  by rewrite (exterior_norm_orthogonal_natural h2 hC hB hJ).
- have [x [hx hValue]]:=operator_norm_attained hNorm.
  exists (exterior_power_map i q x); split.
  + change (exterior_norm h2 hC (exterior_power_map i q x)<=1).
    by rewrite (exterior_norm_orthogonal_natural h2 hB hC hI).
  + change (exterior_norm h2 hD (exterior_power_map g q (exterior_power_map i q x))=L).
    by rewrite hForward.
Qed.
