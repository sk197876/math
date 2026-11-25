(** Federer (1969), 2.10.45, printed pp. 202–203: choose a positive integer
    j(T) whose mesh multiple covers the side length u and is at most u plus
    one mesh. Specify these integer inequalities before proving existence.
    The weak upper bound includes zero side length; for positive side length
    the existence proof gives the printed stronger strict bracket. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_uniform_mesh_count]: supporting
    positive integer subdivision count j(T) for
    the cube cover in 2.10.45, pp. 202–203.
    A supplied positive mesh and nonnegative side
    are external parameters; no ceiling implementation
    or covering conclusion is part of the specification. *)
Record is_uniform_mesh_count (R : realType) (u h : R) (k : nat) : Prop := {
  (** Source for [uniform_mesh_count_positive_law]: direct
      positive integer j(T) in 2.10.45,
      p. 202, final paragraph. *)
  uniform_mesh_count_positive_law : (0<k)%N;
  (** Source for [uniform_mesh_count_covers_law]: direct
      u<=j(T) diam(T) in 2.10.45, p. 202. *)
  uniform_mesh_count_covers_law : u<=k%:R*h;
  (** Source for [uniform_mesh_count_upper_law]: direct
      j(T) diam(T)<=u+diam(T) in 2.10.45,
      p. 203, first displayed bound. *)
  uniform_mesh_count_upper_law : k%:R*h<=u+h
}.
