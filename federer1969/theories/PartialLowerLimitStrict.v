(** Federer (1969), proof of 2.4.6, p. 84: a strict lower bound on the
    pointwise lower limit is eventually a lower bound on every sequence
    value. The argument uses only the abstract lower-limit laws from 2.3.2,
    p. 74. Source context: ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionLimitExtremaUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_lower_limit_strict_eventual_bound]:
    supporting eventual strict inequality for the tail sets in
    Federer 2.4.6, p. 84. Values outside the domain
    are not asserted to exist; the common domain is used separately. *)
Lemma partial_lower_limit_strict_eventual_bound (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) x y b :
  is_partial_function_lower_limit f g -> partial_function_graph g x y -> b < y ->
  exists N, forall n, (N <= n)%N -> forall z, partial_function_graph (f n) x z -> b < z.
Proof.
move=> hg hy hb.
have [he|he] := pselect (exists c, partial_function_eventual_lower_bound f x c /\ b < c).
- have [c [[N hN] hbc]] := he; exists N=> n hn z hz.
  exact: lt_le_trans hbc (hN n hn z hz).
- exfalso; have hle : y <= b.
    apply: (@partial_function_lower_limit_least R X f g hg x y hy b)=> c hc.
    rewrite leNgt; apply/negP=> hbc; apply: he; exists c; by split.
  by move: hb; rewrite ltNge hle.
Qed.
