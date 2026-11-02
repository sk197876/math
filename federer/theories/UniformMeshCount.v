(** Public abstract subdivision counts for Federer (1969), 2.10.45, pp.
    202–203. The count witness is opaque; downstream arguments use only its
    positive covering bracket. Source context: UniformMeshCountUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import UniformMeshCountUP UniformMeshCountSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [uniform_mesh_count]: abstract chosen
    integer j(T) in 2.10.45, pp. 202–203. *)
Definition uniform_mesh_count (R : realType) (u h : R) (hu : 0<=u) (hh : 0<h) :=
  @UniformMeshCount.value R u h hu hh.

(** Source for [uniform_mesh_count_specification]: proved
    positive-count and bracket laws for the cube
    subdivision of 2.10.45, pp. 202–203. *)
Theorem uniform_mesh_count_specification (R : realType) (u h : R) (hu : 0<=u) (hh : 0<h) :
  is_uniform_mesh_count u h (@uniform_mesh_count R u h hu hh).
Proof. exact: UniformMeshCount.laws. Qed.
