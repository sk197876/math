(** Federer (1969), 2.3.2(2), p. 73: sealed dense refinement for the
    arbitrary dense-subset ray criterion. Source context and abstract
    specification: DenseOrderRefinementUP.v. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
From Federer Require Import CountableOrderIntervals DenseOrderRefinementUP DenseOrderRefinementConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type DenseOrderRefinementSignature.
(** Source for [value]: abstract dense family supporting
    Federer 2.3.2(2), p. 73. *)
Parameter value : forall disp (Y : orderTopologicalType disp) (J : Type)
  (d : J -> Y) (D : set Y) (y0 : Y), is_order_dense_family d -> dense D -> D y0 -> J * J -> Y.
(** Source for [laws]: membership and density laws for the
    threshold family supporting Federer 2.3.2(2), p. 73. *)
Parameter laws : forall disp (Y : orderTopologicalType disp) (J : Type)
  (d : J -> Y) (D : set Y) (y0 : Y) (hd : is_order_dense_family d) (hD : dense D) (hy0 : D y0),
  is_dense_order_refinement D (@value disp Y J d D y0 hd hD hy0).
End DenseOrderRefinementSignature.
Module DenseOrderRefinement : DenseOrderRefinementSignature.
(** Source for [value]: private witness selection from the
    dense-family existence proof for Federer 2.3.2(2), p. 73. *)
Definition value disp (Y : orderTopologicalType disp) (J : Type)
  (d : J -> Y) (D : set Y) (y0 : Y) (hd : is_order_dense_family d) (hD : dense D) (hy0 : D y0) :=
  projT1 (cid (@dense_order_refinement_exists disp Y J d D y0 hd hD hy0)).
(** Source for [laws]: the selected family satisfies its
    specification supporting Federer 2.3.2(2), p. 73. *)
Lemma laws disp (Y : orderTopologicalType disp) (J : Type)
  (d : J -> Y) (D : set Y) (y0 : Y) (hd : is_order_dense_family d) (hD : dense D) (hy0 : D y0) :
  is_dense_order_refinement D (@value disp Y J d D y0 hd hD hy0).
Proof. exact: projT2 (cid (@dense_order_refinement_exists disp Y J d D y0 hd hD hy0)). Qed.
End DenseOrderRefinement.
