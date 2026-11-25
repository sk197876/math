(** Federer (1969), 2.10.30, p. 195: compact S has compact Steiner
    symmetrisation T. Use intrinsic normal product coordinates and the
    already proved compact-centred-product theorem. No finite-dimensional
    basis or symmetrisation construction is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import InnerProductUP InnerMetric OrthonormalFamilies RealMetricBackground
  CenteredSectionUP SteinerSymmetrisationUP UnitNormalGeometry NormalProductCoordinates
  ProductSections CompactCenteredProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_preserves_compactness]: direct
    compactness conclusion in 2.10.30, p. 195.
    The proof actually works in any real inner-product
    space when a symmetrisation satisfies the specified
    section laws, including the empty source. *)
Theorem steiner_preserves_compactness (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (u : V) (S T : set (inner_metric_space hB)) :
  is_steiner_symmetrisation hB u S T -> compact S -> compact T.
Proof.
move=> hT hS.
pose E := inner_metric_space hB.
pose F := @normal_product_split R V B hB u.
pose G := @normal_product_join R V B hB u.
have hu := steiner_unit_normal_law hT.
have hK : compact (F @` S).
  apply: continuous_compact _ hS; exact: continuous_subspaceT (@normal_product_split_continuous R V B hB u).
have hsections y : is_centered_section
    (product_vertical_section (F @` S) y) (product_vertical_section (F @` T) y).
  case: (pselect (inner_coordinate hB u y=0))=> [hy|hy].
  - rewrite /F !(@normal_product_image_section R V B hB u _ y hu hy).
    exact (steiner_normal_sections_law hT hy).
  - rewrite /F !(@normal_product_image_off_hyperplane R V B hB u _ y hu hy).
    constructor; [by split=> [[x []]|[x []]]|by move=> [x []]|by []].
have hC := @compact_centered_product R [the topologicalType of E] (F @` S) (F @` T)
  (@metric_hausdorff R E) hK hsections.
have he : G @` (F @` T)=T.
  apply/seteqP; split=> x.
  - move=> [_ [y hy <-] <-]; by rewrite /G /F normal_product_splitK.
  - move=> hx; exists (F x); first by exists x.
    exact: normal_product_splitK.
rewrite -he; apply: continuous_compact _ hC.
exact: continuous_subspaceT (@normal_product_join_continuous R V B hB u).
Qed.
