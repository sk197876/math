(** Federer (1969), 2.6.6, p. 120: finite products of the factor integrals,
    constructed by 2.6.4. This abstract family specification gives the
    empty-product and adjoining-factor laws, together with consistency.
    Existence is proved by iterated integration and hidden behind a seal.
    Source context: CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals topology.
From Federer Require Import ConsistentCylinderFunctionalUP CoordinateDaniellOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope fset_scope.

(** Source for [is_finite_coordinate_product_family]: abstract laws
    for the finite products in Federer 2.6.6, p. 120. Adjoining
    a factor uses the section formula proved in 2.6.4, p. 119;
    no enumeration or particular witness occurs in the specification. *)
Record is_finite_coordinate_product_family (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (C : {fset I} -> (prod_topology Y -> R) -> R) : Prop := {
  (** Source for [finite_coordinate_product_consistency]: normalized
      monotone finite marginals and their consistency, Federer 2.6.6,
      p. 120. *)
  finite_coordinate_product_consistency : is_consistent_cylinder_functional_family C;
  (** Source for [finite_coordinate_product_empty]: the empty product
      acts on constant functions by their value, the boundary case of
      Federer 2.6.6, p. 120. *)
  finite_coordinate_product_empty : forall f, continuous_coordinate_functions fset0 f ->
    forall x, C fset0 f=f x;
  (** Source for [finite_coordinate_product_adjoin]: adjoining one
      factor through the iterated-section formula of 2.6.4, p. 119,
      as used in Federer 2.6.6, p. 120. *)
  finite_coordinate_product_adjoin : forall i F, i \notin F ->
    forall f, continuous_coordinate_functions (i |` F) f ->
    C (i |` F) f=C F (coordinate_daniell_operator A i f)
}.
