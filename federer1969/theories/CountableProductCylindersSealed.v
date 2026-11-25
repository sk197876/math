(** Federer (1969), 2.3.2(5), p. 73: sealed countable refining family of
    finite coordinate cylinders. The private witness construction is not
    exposed to measurable function proofs. Source context:
    CountableProductCylindersUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality topology.
From Federer Require Import CountableOpenBaseUP CountableProductCylindersUP
  CountableProductCylindersConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type CountableProductCylindersSignature.
(** Source for [value]: abstract refining family supporting
    Federer 2.3.2(5), p. 73. *)
Parameter value : forall (I : choiceType) (Y : I -> topologicalType)
  (U : forall i, nat -> set (Y i)), countable (@setT I) ->
  (forall i, is_countable_open_base (U i)) -> set (set (prod_topology Y)).
(** Source for [laws]: proved refinement laws for the family
    supporting Federer 2.3.2(5), p. 73. *)
Parameter laws : forall (I : choiceType) (Y : I -> topologicalType)
  (U : forall i, nat -> set (Y i)) (hi : countable (@setT I))
  (hU : forall i, is_countable_open_base (U i)),
  is_countable_product_cylinder_refinement U (@value I Y U hi hU).
End CountableProductCylindersSignature.
Module CountableProductCylinders : CountableProductCylindersSignature.
(** Source for [value]: private selection of the countable
    refining family proved to exist for Federer 2.3.2(5), p. 73. *)
Definition value (I : choiceType) (Y : I -> topologicalType)
  (U : forall i, nat -> set (Y i)) (hi : countable (@setT I))
  (hU : forall i, is_countable_open_base (U i)) :=
  projT1 (cid (@countable_product_cylinder_refinement_exists I Y U hi hU)).
(** Source for [laws]: the selected family satisfies the abstract
    cylinder-refinement laws supporting Federer 2.3.2(5), p. 73. *)
Lemma laws (I : choiceType) (Y : I -> topologicalType)
  (U : forall i, nat -> set (Y i)) (hi : countable (@setT I))
  (hU : forall i, is_countable_open_base (U i)) :
  is_countable_product_cylinder_refinement U (@value I Y U hi hU).
Proof. exact: projT2 (cid (@countable_product_cylinder_refinement_exists I Y U hi hU)). Qed.
End CountableProductCylinders.
