(** Federer (1969), 1.7.11, p. 36: the inclusion of S times T into V times
    V, with the product restricted metric. Supporting maps for applying the
    identity of 1.6.5 to the difference map on these actual subspace
    carriers. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerProductRestriction ProductInner
  SubspaceDifference OrthogonalMaps ModuleQuotient SubspaceCarrier
  ProductLinearMaps ProductSpaceMaps ExteriorMapScaling ExteriorMaps
  ExteriorGrading ExteriorNormNaturality ExteriorHomogeneousProducts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Inclusion.
Variable R : realFieldType.
Variable V : lmodType R.
Variables S T : subspace V.
Local Notation U := (GRing.Lmodule.clone R (subspace_space S * subspace_space T)%type _).
Local Notation W := (GRing.Lmodule.clone R (V * V)%type _).

(** Source for [subspace_product_inclusion]: Federer 1.7.11,
    p. 36, supporting inclusion sending a pair of subspace
    vectors to the same pair in the ambient Cartesian square. *)
Definition subspace_product_inclusion (z : U) : W :=
  (subspace_val z.1, subspace_val z.2).

(** Source for [subspace_product_inclusion_linear]: Federer
    1.7.11, p. 36, linearity of the Cartesian inclusion. *)
Lemma subspace_product_inclusion_linear : linear subspace_product_inclusion.
Proof.
move=> a x y.
change ((subspace_val (a *: x.1 + y.1), subspace_val (a *: x.2 + y.2)) =
  (a *: subspace_val x.1 + subspace_val y.1, a *: subspace_val x.2 + subspace_val y.2)).
by rewrite !linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R U W *:%R
  subspace_product_inclusion subspace_product_inclusion_linear.

(** Source for [subspace_product_inclusion_orthogonal]: Federer
    1.7.11, p. 36, supporting preservation of the product metric
    by the inclusion of S times T into V times V. *)
Theorem subspace_product_inclusion_orthogonal (B : V -> V -> R)
    (hB : is_inner_product B) :
  is_orthogonal_map (subspace_product_inner hB S T) (product_inner hB hB)
    subspace_product_inclusion.
Proof.
move=> x y; by rewrite /subspace_product_inner !product_innerE
  /restricted_inner_product /subspace_product_inclusion.
Qed.

(** Source for [subspace_difference_factorisation]: Federer
    1.7.11, p. 36, the difference map is the restriction of
    the ambient difference map from 1.6.5, p. 25. *)
Lemma subspace_difference_factorisation z :
  subspace_difference S T z = FedererProduct.f_map V (subspace_product_inclusion z).
Proof. by []. Qed.

(** Source for [subspace_product_exterior_inclusion]: Federer
    1.7.11, p. 36, supporting image of the product volume:
    including its two factors gives the exterior product of their
    ambient images in opposite Cartesian factors, as in 1.6.5. *)
Theorem subspace_product_exterior_inclusion k l
    (x : exterior_power (GRing.Lmodule.clone R (subspace_space S) _) k)
    (y : exterior_power (GRing.Lmodule.clone R (subspace_space T) _) l) :
  exterior_power_map (GRing.Linear.clone _ _ _ _ subspace_product_inclusion _) (k+l)
    (exterior_product
      (exterior_power_map (GRing.Linear.clone _ _ _ _
        (@product_left R (GRing.Lmodule.clone R (subspace_space S) _)
          (GRing.Lmodule.clone R (subspace_space T) _)) _) k x)
      (exterior_power_map (GRing.Linear.clone _ _ _ _
        (@product_right R (GRing.Lmodule.clone R (subspace_space S) _)
          (GRing.Lmodule.clone R (subspace_space T) _)) _) l y)) =
  exterior_product
    (exterior_power_map (FedererProduct.P_map V) k
      (exterior_power_map (GRing.Linear.clone _ _ _ _ (@subspace_val R V S) _) k x))
    (exterior_power_map (FedererProduct.Q_map V) l
      (exterior_power_map (GRing.Linear.clone _ _ _ _ (@subspace_val R V T) _) l y)).
Proof.
rewrite exterior_power_map_product !exterior_power_map_composition.
congr (exterior_product _ _); apply: exterior_power_map_ext => z.
- change ((subspace_val z, subspace_val (0 : subspace_space T)) = (subspace_val z,0)).
  by rewrite linear0.
- change ((subspace_val (0 : subspace_space S), subspace_val z) = (0,subspace_val z)).
  by rewrite linear0.
Qed.
End Inclusion.

Arguments subspace_product_inclusion {R V} S T _.
