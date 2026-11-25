(** Federer (1969), 2.6.6, p. 120: uniqueness of the normalized monotone
    Daniell functional with the prescribed finite marginals. The proof uses
    actual uniform density and the abstract norm-one continuity bound.
    Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP ProductCylinderLattice ProductCylinderDensity
  CylinderDaniellExtensionUP NormalizedDaniellUniformLipschitz CompactUniformNorm UniformFunctionNorm
  FunctionSeminormDistance ScalarLipschitzExtensionUP DenseScalarExtensionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cylinder_daniell_extension_unique]: the final
    uniqueness assertion in Federer 2.6.6, p. 120, on K(X).
    Values of ambient representatives outside K(X) are irrelevant. *)
Theorem cylinder_daniell_extension_unique (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (x0 : prod_topology Y)
    (C : {fset I} -> (prod_topology Y -> R) -> R)
    (B D : (prod_topology Y -> R) -> R) :
  compact (@setT (prod_topology Y)) ->
  is_cylinder_daniell_extension C B -> is_cylinder_daniell_extension C D ->
  forall f, compactly_supported_continuous_functions f -> B f=D f.
Proof.
move=> hc [hB [hB1 hBC]] [hD [hD1 hDC]].
pose K := @compactly_supported_continuous_functions R (prod_topology Y).
pose L := @continuous_product_cylinders R I Y.
pose d := function_seminorm_distance (@compact_support_uniform_norm R (prod_topology Y)).
have hd := @function_seminorm_distance_laws R (prod_topology Y) K _
  (@compact_support_vector_lattice R (prod_topology Y)) (@compact_support_uniform_norm_laws R (prod_topology Y)).
have hLK : forall f, L f -> K f by move=> f hf; exact: hf.1.
have hBd := normalized_daniell_uniform_lipschitz hc hB hB1.
have hDd := normalized_daniell_uniform_lipschitz hc hD hD1.
have heB : is_scalar_lipschitz_extension K L d B B by split.
have heD : is_scalar_lipschitz_extension K L d B D.
  split=> // f [hf [F hF]]; by rewrite (hDC F f (conj hf hF)) (hBC F f (conj hf hF)).
exact: (@dense_scalar_lipschitz_extension_unique R _ K L d B B D hd hLK
  (@compact_product_cylinders_uniformly_dense R I Y x0 hc) heB heD).
Qed.
