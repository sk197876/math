(** Federer (1969), 2.6.6, p. 120: p_a induces a monomorphism from K(X_a) to
    K(X), with image L_a. These lemmas identify that image with the abstract
    coordinate-dependence domain used for the finite marginals. Source
    context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import CompactContinuousPullback CompactSupportFunctionUP ProductCylinderLattice FiniteCoordinateProjection
  ConsistentCylinderFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_coordinate_product_compact]: compactness of
    X_a in Federer 2.6.6, p. 120, also following from the
    continuous surjection p_a from the compact full product. *)
Lemma finite_coordinate_product_compact (I : choiceType) (Y : I -> topologicalType)
    (x0 : prod_topology Y) (F : {fset I}) :
  compact (@setT (prod_topology Y)) -> compact (@setT (finite_coordinate_space Y F)).
Proof.
move=> hc.
have hi : compact (finite_coordinate_projection (Y:=Y) (F:=F) @` setT).
  apply: continuous_compact _ hc; exact: continuous_subspaceT (@finite_coordinate_projection_continuous I Y F).
have he : finite_coordinate_projection (Y:=Y) (F:=F) @` setT = [set: finite_coordinate_space Y F].
  apply/seteqP; split=> u; first by [].
  move=> _; exists (finite_coordinate_section x0 u)=> //; exact: finite_coordinate_section_projection.
by rewrite he in hi.
Qed.

(** Source for [finite_coordinate_pullback_membership]: p_a
    maps K(X_a) into the coordinate-dependence form of L_a,
    Federer 2.6.6, p. 120. *)
Lemma finite_coordinate_pullback_membership (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (F : {fset I}) (g : finite_coordinate_space Y F -> R) :
  compact (@setT (prod_topology Y)) -> compactly_supported_continuous_functions g ->
  continuous_coordinate_functions F (g \o finite_coordinate_projection (F:=F)).
Proof.
move=> hc hg; split.
- exact (@compact_continuous_pullback_membership R (prod_topology Y) (finite_coordinate_space Y F)
    (@finite_coordinate_projection I Y F) g hc (@finite_coordinate_projection_continuous I Y F) hg).
- move=> x y hxy; congr g; apply: functional_extensionality_dep=> i.
  exact: hxy (val i) (valP i).
Qed.

(** Source for [finite_coordinate_cylinder_image]: exact image L_a
    of K(X_a) under pullback by p_a in Federer 2.6.6, p. 120.
    The converse is supplied by the continuous coordinate section. *)
Theorem finite_coordinate_cylinder_image (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (x0 : prod_topology Y) (F : {fset I}) (f : prod_topology Y -> R) :
  compact (@setT (prod_topology Y)) ->
  (continuous_coordinate_functions F f <->
    exists g : finite_coordinate_space Y F -> R,
      compactly_supported_continuous_functions g /\ f=g \o finite_coordinate_projection (F:=F)).
Proof.
move=> hc; split.
- move=> [hf hdep]; exists (f \o finite_coordinate_section x0 (F:=F)); split.
  + exact (@compact_continuous_pullback_membership R (finite_coordinate_space Y F) (prod_topology Y)
      (@finite_coordinate_section I Y x0 F) f (@finite_coordinate_product_compact I Y x0 F hc)
      (@finite_coordinate_section_continuous I Y x0 F) hf).
  + exact: coordinate_determined_factorization hdep.
- move=> [g [hg ->]]; exact: finite_coordinate_pullback_membership hc hg.
Qed.
