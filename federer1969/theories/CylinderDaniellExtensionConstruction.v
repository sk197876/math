(** Private extension construction for Federer (1969), 2.6.6, p. 120: glue
    consistent finite marginals, then extend using the proved uniform
    density of cylinders. This theorem handles a supplied consistent family;
    actual product-family existence is established separately. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP DaniellSpaceCompactSpace ProductCylinderLattice ProductCylinderDensity
  ConsistentCylinderFunctionalUP CylinderFunctionalGluingConstruction CylinderFunctionalGluingLaws
  CompactDenseDaniellExtension CylinderDaniellExtensionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cylinder_daniell_extension_exists]: existence of
    the Daniell extension with all prescribed finite marginals,
    Federer 2.6.6, p. 120. Compactness and actual cylinder
    density are proved inputs, not assumed extension axioms. *)
Theorem cylinder_daniell_extension_exists (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (x0 : prod_topology Y)
    (C : {fset I} -> (prod_topology Y -> R) -> R) :
  hausdorff_space (prod_topology Y) -> compact (@setT (prod_topology Y)) ->
  is_consistent_cylinder_functional_family C -> exists B, is_cylinder_daniell_extension C B.
Proof.
move=> hh hc hC; have [G hG] := cylinder_functional_gluing_exists hC.
have hD1 : @continuous_product_cylinders R I Y (fun _=>1).
  split; first exact: (@compact_space_constant_one R (prod_topology Y) hc).
  by exists fset0.
have hDK : forall f, @continuous_product_cylinders R I Y f -> compactly_supported_continuous_functions f.
  by move=> f hf; exact: hf.1.
have [B [hB [hB1 hext]]] := @compact_dense_daniell_extension_exists R (prod_topology Y)
  (@continuous_product_cylinders R I Y) G hh hc (@continuous_product_cylinders_vector_lattice R I Y)
  hD1 hDK (@compact_product_cylinders_uniformly_dense R I Y x0 hc)
  (glued_cylinder_functional_linear hC hG) (glued_cylinder_functional_one hC hG hc)
  (glued_cylinder_functional_norm_bound hC hG hc).
exists B; split=> //; split=> // F f [hf hdep].
have hDf : continuous_product_cylinders f by split=> //; exists F.
by rewrite (hext.1 _ hDf) (hG F f (conj hf hdep)).
Qed.
