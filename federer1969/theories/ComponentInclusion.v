(** Federer (1969), 4.1.4, pp. 348–349: the component
    of the same centre grows when its ambient open set grows.
    This general-topology support uses only the existing
    maximality and symmetry laws of connected components. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [component_inclusion]: ambient inclusion gives
    component inclusion, the monotonicity used for C_e in
    Federer 4.1.4, pp. 348–349. *)
Theorem component_inclusion (T:topologicalType) (A B:set T) (a:T):
  A `<=` B ->connected_component A a `<=` connected_component B a.
Proof.
move=>hAB x hx.
have hBase:A a:=@connected_component_sub T A x a (@connected_component_sym T A a x hx).
have hCover:connected_component A a `<=` B.
  move=>y hy; exact:hAB y (@connected_component_sub T A a y hy).
exact:(@connected_component_max T B (connected_component A a) a
  (connected_component_refl hBase) hCover (@component_connected T A a) x hx).
Qed.
