(** Federer (1969), 2.4.12, p. 87: the infinity-endpoint completeness
    argument through convergence in measure and an almost-everywhere
    convergent subsequence. These statements retain partial domains and
    allow infinite individual norms; membership in the finite-norm Lebesgue
    space is a separate condition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBoundsUP ExtendedLowerLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_lower_limit_eventual_upper_bound]:
    supporting eventual upper bound on the lower limit in the
    completeness proof of Federer 2.4.12, p. 87. *)
Lemma extended_lower_limit_eventual_upper_bound (R : realType) (u : nat -> \bar R) a b :
  is_extended_lower_limit u a ->
  (exists K, forall n, (K <= n)%N -> u n <= b) -> a <= b.
Proof.
move=> ha [K hK]; apply: (extended_real_supremum_least ha)=> c [M hM].
exact: le_trans (hM (maxn M K) (leq_maxl M K)) (hK (maxn M K) (leq_maxr M K)).
Qed.
