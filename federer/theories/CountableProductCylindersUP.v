(** Federer (1969), 2.3.2(5), p. 73: countable products of spaces with
    countable bases. We specify a countable refining family of precisely
    such intersections. General product topology is background; no external
    measurable-product theorem is used. *)
From mathcomp Require Import all_boot finmap classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [product_coordinate_cylinders]: supporting basic cylinders in
    the proof of Federer 2.3.2(5), p. 73. *)
Definition product_coordinate_cylinders (I : choiceType) (Y : I -> topologicalType)
    (U : forall i, nat -> set (Y i)) : set (set (prod_topology Y)) :=
  \bigcup_i [set [set y : prod_topology Y | U i n (y i)] | n in setT].

(** Source for [is_countable_product_cylinder_refinement]: abstract
    supporting specification for the finite-cylinder argument in Federer
    2.3.2(5), p. 73 Empty finite intersections are included, also for empty
    I. *)
Record is_countable_product_cylinder_refinement (I : choiceType)
    (Y : I -> topologicalType) (U : forall i, nat -> set (Y i))
    (B : set (set (prod_topology Y))) : Prop := {
  (** Source for [product_cylinder_refinement_countable]: countable
      family in the proof of Federer 2.3.2(5), p. 73. *)
  product_cylinder_refinement_countable : countable B;
  (** Source for [product_cylinder_refinement_finite]: finite cylinder
    intersections in Federer 2.3.2(5), p. 73. *)
  product_cylinder_refinement_finite : B `<=` finI_from (product_coordinate_cylinders U) id;
  (** Source for [product_cylinder_refinement_local]: refinement
      of open neighborhoods supporting Federer 2.3.2(5), p. 73. *)
  product_cylinder_refinement_local : forall V, open V -> forall x, V x ->
    exists W, B W /\ W x /\ W `<=` V
}.
