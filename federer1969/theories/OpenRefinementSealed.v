(** Federer (1969), 2.2.9, p. 65: sealed existence of a countable disjoint
    open refinement. The private remainder recursion is hidden, exposing
    only the refinement laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import NoIsolatedPoints OpenRefinementUP OpenRefinementConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type OpenRefinementSignature.
(** Source for [value]: supporting open children for Federer
    2.2.9, p. 65, selected for any nonempty open parent and
    positive diameter tolerance. *)
Parameter value : forall (R : realType) (T : metricType R),
  has_no_isolated_points T -> forall U : set T,
  open U -> U !=set0 -> forall e : R, 0 < e -> nat -> set T.
(** Source for [laws]: Federer 2.2.9, p. 65, the abstract
    open-refinement laws of the selected children. *)
Parameter laws : forall (R : realType) (T : metricType R)
  (hT : has_no_isolated_points T) (U : set T)
  (ho : open U) (hn : U !=set0) (e : R) (he : 0 < e),
  is_open_disjoint_refinement U e (@value R T hT U ho hn e he).
End OpenRefinementSignature.
Module OpenRefinement : OpenRefinementSignature.
(** Source for [value]: supporting witness selection for
    Federer 2.2.9, p. 65, from the proved refinement existence theorem. *)
Definition value (R : realType) (T : metricType R)
    (hT : has_no_isolated_points T) (U : set T)
    (ho : open U) (hn : U !=set0) (e : R) (he : 0 < e) :=
  projT1 (cid (open_disjoint_refinement_exists hT ho hn he)).
(** Source for [laws]: Federer 2.2.9, p. 65, the selected
    witness discharges the abstract refinement specification. *)
Lemma laws (R : realType) (T : metricType R)
    (hT : has_no_isolated_points T) (U : set T)
    (ho : open U) (hn : U !=set0) (e : R) (he : 0 < e) :
  is_open_disjoint_refinement U e (@value R T hT U ho hn e he).
Proof. exact: projT2 (cid (open_disjoint_refinement_exists hT ho hn he)). Qed.
End OpenRefinement.
