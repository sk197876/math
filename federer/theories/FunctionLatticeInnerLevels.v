(** Federer (1969), 2.5.3, p. 94, first further condition: inner
    approximations by closed unit levels with an F1 set removed. The
    predicates here specify that supporting supremum, before proving the
    full difference-set assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [function_lattice_inner_unit_values]: Supporting Federer
    2.5.3, p. 94. *)
Definition function_lattice_inner_unit_values (R : realType) (X : Type)
    (L : set (X -> R)) (mu : set X -> \bar R) (V : set X) :=
  [set a | exists h : X -> R, positive_function_lattice L h /\
    [set x | (1 <= h x)%R] `<=` V /\ a=mu [set x | (1 <= h x)%R]].
