(** Federer (1969), 2.3.10, p. 80: elementary consequences of the strictly
    increasing index selection. Source context: CauchyIndexSelectionUP.v. *)
From mathcomp Require Import all_boot all_order classical_sets reals constructive_ereal.
From Federer Require Import CauchyIndexSelectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [strict_index_sequence_dominates]: supporting
    cofinality of the chosen subsequence in Federer 2.3.10,
    p. 80: its n-th index is at least n. *)
Lemma strict_index_sequence_dominates (s : nat -> nat) :
  (forall n, (s n < s n.+1)%N) -> forall n, (n <= s n)%N.
Proof.
move=> hs; elim=> [|n ih]; first exact: leq0n.
have hstep : (n.+1 <= (s n).+1)%N := ih.
exact: leq_trans hstep (hs n).
Qed.

(** Source for [cauchy_index_successive_bound]: the successive
    distances of the selected subsequence satisfy the assigned
    summable bounds, as in Federer 2.3.10, p. 80. *)
Lemma cauchy_index_successive_bound (R : realType) (d : nat -> nat -> \bar R)
    (b : nat -> R) (s : nat -> nat) :
  is_cauchy_index_selection d b s -> forall n, d (s n.+1) (s n) < (b n)%:E.
Proof. move=> [hs hb] n; exact: hb n _ _ (ltnW (hs n)) (leqnn _). Qed.
