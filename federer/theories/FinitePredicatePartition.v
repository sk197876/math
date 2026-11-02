(** Federer (1969), 1.7.3, p. 30: supporting finite indexing of nonzero
    images and kernel basis vectors. These are finite-set infrastructure
    lemmas, not separate claims in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Partition.
Variable I : finType.
Variable P : pred I.
Local Notation J := (Finite.clone {i : I | P i} _).
Local Notation K := (Finite.clone {i : I | ~~ P i} _).

(** Source for [predicate_partition_rank]: Federer 1.7.3,
    p. 30, supporting enumeration with the prescribed-image
    indices first and the remaining indices second. *)
Definition predicate_partition_rank (i : I) : 'I_(#|J| + #|K|).
Proof.
case: (pselect (P i)) => hi.
- exact (lshift #|K| (enum_rank (Sub i hi : J))).
- exact (rshift #|J| (enum_rank (Sub i (introT (@negP (P i)) hi) : K))).
Defined.

(** Source for [predicate_partition_positive]: Federer 1.7.3,
    p. 30, supporting position of a prescribed-image index. *)
Lemma predicate_partition_positive (i : J) :
  predicate_partition_rank (val i) = lshift #|K| (enum_rank i).
Proof.
rewrite /predicate_partition_rank; case: pselect => hi.
- congr (lshift _ (enum_rank _)); exact: val_inj.
- exfalso; exact: hi (valP i).
Qed.

(** Source for [predicate_partition_negative]: Federer 1.7.3,
    p. 30, supporting position of a complementary index. *)
Lemma predicate_partition_negative (i : K) :
  predicate_partition_rank (val i) = rshift #|J| (enum_rank i).
Proof.
rewrite /predicate_partition_rank; case: pselect => hi.
- by have := valP i; rewrite hi.
- congr (rshift _ (enum_rank _)); exact: val_inj.
Qed.

(** Source for [predicate_partition_injective]: Federer
    1.7.3, p. 30, supporting fact that the two blocks enumerate
    distinct original indices without collisions. *)
Lemma predicate_partition_injective : injective predicate_partition_rank.
Proof.
move=> i j; rewrite /predicate_partition_rank.
case: (pselect (P i)) => hi; case: (pselect (P j)) => hj.
- move/lshift_inj/enum_rank_inj=> hh; exact (congr1 val hh).
- move/(congr1 val)=> /= hh.
  have hlt := ltn_ord (enum_rank (Sub i hi : J)).
  have hle : (#|J| <= #|J| + enum_rank (Sub j (introT (@negP (P j)) hj) : K))%N := leq_addr _ _.
  by rewrite -hh in hle; move: hlt; rewrite ltnNge hle.
- move/(congr1 val)=> /= hh.
  have hlt := ltn_ord (enum_rank (Sub j hj : J)).
  have hle : (#|J| <= #|J| + enum_rank (Sub i (introT (@negP (P i)) hi) : K))%N := leq_addr _ _.
  by rewrite hh in hle; move: hlt; rewrite ltnNge hle.
- move/rshift_inj/enum_rank_inj=> hh; exact (congr1 val hh).
Qed.

(** Source for [predicate_partition_size]: Federer 1.7.3,
    p. 30, the two complementary index blocks have total size
    equal to the original finite index type. *)
Lemma predicate_partition_size : (#|J| + #|K|)%N = #|I|.
Proof. by rewrite !card_sub cardC. Qed.
End Partition.
