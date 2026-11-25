(** Federer (1969), 4.1.1, p. 344: ordinary
    natural partial sums in the locally finite smooth
    sequence argument. This adapter connects the existing
    finite-family sum interface with ordinal prefixes. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets.
From Federer Require Import CountableFiniteExhaustionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [finite_nat_prefix_set]: the finite set
    of original indices less than N, supporting
    the sequence argument in Federer 4.1.1,
    p. 344. *)
Definition finite_nat_prefix_set N:{fset nat}:=seq_fset tt (iota 0 N).

(** Source for [finite_nat_prefix_member]: the exact
    index bound in a natural partial sum,
    supporting Federer 4.1.1, p. 344. *)
Lemma finite_nat_prefix_member N j:(j \in finite_nat_prefix_set N)=(j<N)%N.
Proof. by rewrite /finite_nat_prefix_set seq_fsetE mem_iota add0n leq0n. Qed.

(** Source for [finite_nat_prefix_sum]: the finite-set
    and ordinary ordinal partial sums agree,
    supporting Federer 4.1.1, p. 344. *)
Lemma finite_nat_prefix_sum (V:zmodType) (f:nat->V) N:
  \sum_(j<-finite_nat_prefix_set N) f j=\sum_(j<N) f j.
Proof.
transitivity (\sum_(0<=j<N) f j).
- have hPerm:perm_eq (finite_nat_prefix_set N : seq nat) (iota 0 N).
    have hp:=seq_fset_perm tt (iota 0 N).
    rewrite (undup_id (iota_uniq 0 N)) in hp; exact hp.
  rewrite /index_iota subn0.
  exact (perm_big (r1:=(finite_nat_prefix_set N : seq nat)) (iota 0 N) (P:=xpredT) (F:=f) hPerm).
- exact:big_mkord.

Qed.

(** Source for [finite_nat_prefix_exhaustion]: ordinary
    natural prefixes satisfy the original abstract finite
    exhaustion laws, supporting the sum argument in
    Federer 4.1.1, p. 344, by 2.4.8. *)
Theorem finite_nat_prefix_exhaustion:is_countable_finite_exhaustion (@setT nat) finite_nat_prefix_set.
Proof.
constructor.
- apply/fsetP=>j; by rewrite finite_nat_prefix_member in_fset0 ltn0.
- by move=>n j hj.
- move=>m n hmn; apply/fsubsetP=>j.
  rewrite !finite_nat_prefix_member=>hj; exact:leq_trans hj hmn.
- move=>j _; exists j.+1; by rewrite finite_nat_prefix_member ltnS.
Qed.
