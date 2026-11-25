(** Federer (1969), 3.3.4, p. 291: the measures
    psi_v are pointwise suprema of weighted image measures.
    Specify that supremum independently by its order laws;
    outer-measure laws are conclusions for nonempty families. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_measure_family_supremum]: supporting the
    displayed definition of psi_v in Federer 3.3.4,
    p. 291. For every test set its value is the
    least upper bound of the original component values.
    No regularity, finiteness or outer-measure law is assumed. *)
Definition is_measure_family_supremum (R:realType) (X J:Type)
    (D:set J) (nu:J->set X->\bar R) (psi:set X->\bar R):Prop:=
  forall A,is_extended_real_supremum [set z|exists j,D j /\ z=nu j A] (psi A).
