(** Set-theoretic support for the pointwise sum in Federer (1969), 2.4.8, p.
    84: at a common domain point one may select all summand values. The
    proof uses the project's permitted classical choice principle; it adds
    no project axiom. Values outside the indexing set are irrelevant and may
    be chosen as zero. Source context: PartialNumericalSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_family_common_values_exists]: supporting
    simultaneous value selection on the common domain of the
    summands in Federer 2.4.8, p. 84. *)
Lemma partial_family_common_values_exists (R : realType) (X J : Type)
    (D : set J) (f : J -> partial_function X (extended_real_line R)) x :
  partial_function_common_domain D f x -> exists u : J -> \bar R,
    forall j, D j -> partial_function_graph (f j) x (u j).
Proof.
move=> hx.
have hex j : exists z : \bar R, D j -> partial_function_graph (f j) x z.
  have [hj|hj] := pselect (D j).
  - have [z hz] := hx j hj; exists z; by move=> _.
  - exists 0=> hd; exfalso; exact: hj hd.
exists (fun j => projT1 (cid (hex j)))=> j; exact: projT2 (cid (hex j)).
Qed.
