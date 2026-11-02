(** Private recurrence witness for the sufficient
    partition derivative constants used in Federer
    (1969), 3.1.13, p. 225. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import PartitionDerivativeBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [partition_derivative_prefix]:
    a finite recurrence implementation for the
    constants V_i in Federer 3.1.13,
    p. 225. Prefix values are
    shown stable before the witness is sealed. *)
Fixpoint partition_derivative_prefix (R : realType) (C : R)
    (G : nat->R) n : nat->R :=
  if n is k.+1 then
    fun i=>if i==k.+1 then G k.+1+C*\sum_(j<k.+1)
      ('C(k.+1,k.+1-j))%:R*(G (k.+1-j)%N*partition_derivative_prefix C G k j)
    else partition_derivative_prefix C G k i
  else fun _=>1.

(** Source for [partition_derivative_prefix_stable]:
    later recurrence steps preserve earlier
    constants, supporting the sufficient choice
    in Federer 3.1.13, p. 225. *)
Lemma partition_derivative_prefix_stable (R : realType) C (G : nat->R) n i :
  (i<=n)%N ->
  partition_derivative_prefix C G n i=partition_derivative_prefix C G i i.
Proof.
elim:n=>[hi|n ih hi].
- by move:hi; rewrite leqn0=>/eqP ->.
- case:(eqVneq i n.+1)=>[-> //|hne].
  rewrite /= (negbTE hne).
  apply: ih; by move:hi; rewrite leq_eqVlt (negbTE hne) /= ltnS.
Qed.

(** Source for [partition_derivative_bounds_exists]:
    existence of constants V_i with the
    prescribed sufficient recurrence, supporting
    Federer 3.1.13, p. 225.
    This proof supplies the opaque interface;
    it introduces no recurrence axiom. *)
Theorem partition_derivative_bounds_exists (R : realType) C (G : nat->R) :
  exists V, is_partition_derivative_bounds C G V.
Proof.
exists (fun i=>partition_derivative_prefix C G i i).
split; first by [].
move=>n; rewrite /= eqxx; congr (G n.+1+C*_).
apply: eq_bigr=>j _.
rewrite (partition_derivative_prefix_stable _ _); first by [].
by rewrite -ltnS ltn_ord.
Qed.
