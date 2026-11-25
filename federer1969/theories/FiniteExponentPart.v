(** Federer (1969), 2.4.17, p. 90: the finite exponents used to approach the
    closure of P. This supporting definition keeps that distinction
    explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_exponent_part]: Supporting Federer 2.4.17, p. 90. *)
Definition finite_exponent_part (R : realType) (P : set (\bar R)) : set (extended_real_line R) :=
  [set p | P p /\ p \is a fin_num].
