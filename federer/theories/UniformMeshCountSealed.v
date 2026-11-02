(** Opaque positive integer mesh counts for Federer (1969), 2.10.45, pp.
    202–203. Expose only a count and its proved bracket laws. Source
    context: UniformMeshCountUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import UniformMeshCountUP UniformMeshCountConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type UNIFORM_MESH_COUNT.
(** Source for [value]: abstract integer j(T)
    for 2.10.45, pp. 202–203. *)
Parameter value : forall (R : realType) (u h : R), 0<=u -> 0<h -> nat.
(** Source for [laws]: abstract positive-count and
    covering bracket laws in 2.10.45, pp. 202–203. *)
Parameter laws : forall (R : realType) (u h : R) (hu : 0<=u) (hh : 0<h),
  is_uniform_mesh_count u h (@value R u h hu hh).
End UNIFORM_MESH_COUNT.
Module UniformMeshCount : UNIFORM_MESH_COUNT.
(** Source for [value]: privately proved integer
    witness for 2.10.45, pp. 202–203,
    hidden by opaque module ascription. *)
Definition value (R : realType) (u h : R) (hu : 0<=u) (hh : 0<h) :=
  projT1 (cid (@uniform_mesh_count_exists R u h hu hh)).
(** Source for [laws]: proved subdivision count
    laws for 2.10.45, pp. 202–203. *)
Lemma laws (R : realType) (u h : R) (hu : 0<=u) (hh : 0<h) :
  is_uniform_mesh_count u h (@value R u h hu hh).
Proof. exact: (projT2 (cid (@uniform_mesh_count_exists R u h hu hh))). Qed.
End UniformMeshCount.
