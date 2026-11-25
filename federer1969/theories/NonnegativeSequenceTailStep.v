(** Federer (1969), 2.3.9, p. 79: separating the first term of a series
    tail. This supporting consequence of 2.1.1(9), p. 53, permits a
    telescoping distance estimate without importing an external series
    theorem. Source context: NonnegativeSequenceTail.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumRestriction NonnegativeSequenceTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sequence_tail_step]: a tail equals
    its first term plus the next tail, supporting the Cauchy
    estimate in Federer 2.3.9, p. 79. *)
Lemma nonnegative_sequence_tail_step (R : realType) (a : nat -> \bar R) j :
  (forall n, 0 <= a n) -> nonnegative_sequence_tail a j = a j + nonnegative_sequence_tail a j.+1.
Proof.
move=> ha.
have hi : [set n : nat | (j <= n)%N] `&` [set j] = [set j].
  apply/seteqP; split=> n; first by move=> [_ hn].
  move=> ->; split=> //; exact: leqnn.
have hd : [set n : nat | (j <= n)%N] `\` [set j] = [set n : nat | (j.+1 <= n)%N].
  apply/seteqP; split=> n.
  - move=> [hn hne]; change (j < n)%N; rewrite ltn_neqAle hn andbT.
    apply/eqP=> he; apply: hne; exact: esym he.
  - move=> hn; split; first exact: ltnW hn.
    move=> he; have hn' : (j < n)%N := hn; by rewrite he ltnn in hn'.
rewrite /nonnegative_sequence_tail (@nonnegative_sum_split R nat [set n | (j <= n)%N] [set j] a) //.
by rewrite hi hd nonnegative_sum_singleton.
Qed.
