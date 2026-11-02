(** Federer (1969), 1.8.1, p. 39: the binomial constant in the comass
    product inequality counts the shuffles in 1.4.2, p. 18. Only the upper
    cardinal bound is needed here. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import ExteriorIndices Shuffles ShuffleUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Cardinality.
Variables p q : nat.

(** Source for [shuffle_first_block_size]: Federer 1.8.1,
    p. 39, supporting count: the first block has exactly p entries. *)
Lemma shuffle_first_block_size (s : Sh p q) :
  size (take p (permutation_sequence (val s))) == p.
Proof. by rewrite size_take_min size_tuple (minn_idPl (leq_addr q p)). Qed.

(** Source for [shuffle_first_block]: Federer 1.8.1, p. 39,
    supporting injection from shuffles to increasing p-tuples. *)
Definition shuffle_first_block (s : Sh p q) : Lambda (p+q) p :=
  Sub (Tuple (shuffle_first_block_size s)) (andP (valP s)).1.

(** Source for [shuffle_first_block_injective]: Federer 1.8.1,
    p. 39, the increasing first block determines the shuffle, since
    the second block is the increasing complementary sequence. *)
Lemma shuffle_first_block_injective : injective shuffle_first_block.
Proof.
move=> s t h; apply: shuffle_take_injective.
exact: (congr1 (fun z : Lambda (p+q) p => val (val z)) h).
Qed.

(** Source for [shuffle_cardinality_bound]: Federer 1.8.1,
    p. 39, supporting bound on the number of summands in the
    comass product estimate by binomial(p+q,p). *)
Theorem shuffle_cardinality_bound : #|{: Sh p q}| <= 'C(p+q,p).
Proof.
rewrite -card_Lambda; exact: leq_card (shuffle_first_block_injective).
Qed.
End Cardinality.
