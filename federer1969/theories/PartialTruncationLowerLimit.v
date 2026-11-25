(** Federer (1969), 2.4.11, proof p. 86: the truncations converge
    increasingly to the original nonnegative function. This supporting graph
    statement supplies the exact lower-limit premise for 2.4.7 without
    changing domains. Source context: PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionLimitExtremaUP
  PartialUpperTruncation ExtendedTruncationLimit ExtendedRealBoundsUP ExtendedLowerLimitUP ExtendedConvergentLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_upper_truncation_lower_limit]: exact
    lower-limit specification for the sequence in Federer
    2.4.11, proof p. 86, on its original domain. *)
Lemma partial_upper_truncation_lower_limit (R : realType) (X : Type)
    (f : partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit (fun n => partial_upper_truncation f (n.+1)%:R%:E) f.
Proof.
constructor.
- apply/seteqP; split=> x.
  + move=> hx; exists 0%N=> n _; by rewrite partial_upper_truncation_domain.
  + move=> [N hN]; have hh := hN N (leqnn N); by rewrite partial_upper_truncation_domain in hh.
- move=> x z hz b [N hN].
  have hl := extended_convergent_lower_limit (extended_natural_upper_truncations_increase z).2.
  apply: (extended_lower_limit_eventual_bound hl); exists N=> n hn.
  have hgn : partial_function_graph (partial_upper_truncation f (n.+1)%:R%:E) x
      (Order.min z (n.+1)%:R%:E) by exists z; split.
  exact (hN n hn _ hgn).
- move=> x z hz b hb.
  have hl := extended_convergent_lower_limit (extended_natural_upper_truncations_increase z).2.
  apply: (extended_real_supremum_least hl)=> c [N hN]; apply: hb; exists N=> n hn y [w [hw ewy]].
  have ezw := partial_function_single_valued hz hw.
  by rewrite -ewy -ezw; exact: hN n hn.
Qed.
