(** Federer (1969), 2.4.17, p. 90: the empty and isolated infinity exponent
    cases. This supporting topology lemma handles every subset of that
    singleton, including empty P. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import CountableOrderIntervals ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinity_supported_closure_continuous]: Supporting Federer
    2.4.17, p. 90.Any function is continuous on the closure of such a
    domain. *)
Lemma infinity_supported_closure_continuous (R : realType) (Z : topologicalType)
    (P : set (extended_real_line R)) (f : extended_real_line R -> Z) :
  (forall p, P p -> p=+oo) -> continuous (f : subspace (closure P) -> Z).
Proof.
move=> hP.
have hsub : P `<=` [set p : extended_real_line R | +oo <= p] by move=> p hp; rewrite (hP p hp).
have hclosed : closed [set p : extended_real_line R | +oo <= p] :=
  @order_closed_upper_ray_closed _ [the orderTopologicalType _ of order_topology (\bar R)] +oo.
have hcl p : closure P p -> p=+oo.
  move=> hp; have hh := hclosed p (closureS hsub hp).
  by apply/eqP; rewrite eq_le leey hh.
apply/subspace_continuousP=> x hx B hB.
change (nbhs x [set y | closure P y -> B (f y)]).
apply: filterE=> y hy; rewrite (hcl y hy) -(hcl x hx).
exact: nbhs_singleton hB.
Qed.
