(** Supporting finite coordinates for Federer (1969),
    3.4.8(8), pp. 329–330: place the
    original suffix first when applying the
    existing prefix-sphere coordinate theorems. *)
From mathcomp Require Import all_boot all_order.
From Federer Require Import OrdinalCoordinateTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [ordinal_two_block_exchange]: interchange
    the two original coordinate blocks,
    supporting the suffix-sphere identification in
    3.4.8(8), pp. 329–330. This is
    a prescribed finite index map. *)
Definition ordinal_two_block_exchange p q (i:'I_(p+q)):'I_(q+p):=
  match split i with
  |inl j=>rshift q j
  |inr j=>lshift p j
  end.

(** Source for [ordinal_two_block_exchange_left]: first
    block indices become last block indices,
    supporting 3.4.8(8), pp. 329–330. *)
Lemma ordinal_two_block_exchange_left p q (i:'I_p):
  ordinal_two_block_exchange (lshift q i) = rshift q i.
Proof.
change (match split (unsplit (inl i:'I_p+'I_q)) with
  |inl j=>rshift q j|inr j=>lshift p j end = rshift q i).
by rewrite unsplitK.
Qed.

(** Source for [ordinal_two_block_exchange_right]: last
    block indices become first block indices,
    supporting 3.4.8(8), pp. 329–330. *)
Lemma ordinal_two_block_exchange_right p q (i:'I_q):
  ordinal_two_block_exchange (rshift p i) = lshift p i.
Proof.
change (match split (unsplit (inr i:'I_p+'I_q)) with
  |inl j=>rshift q j|inr j=>lshift p j end = lshift p i).
by rewrite unsplitK.
Qed.

(** Source for [ordinal_two_block_exchange_cancel]: exchange
    the same two blocks back, supporting
    the original coordinate isometry in
    3.4.8(8), pp. 329–330. *)
Lemma ordinal_two_block_exchange_cancel p q:
  cancel (@ordinal_two_block_exchange p q) (@ordinal_two_block_exchange q p).
Proof.
move=>i;case:(split_ordP i)=>[j ->|j ->].
- by rewrite ordinal_two_block_exchange_left ordinal_two_block_exchange_right.
- by rewrite ordinal_two_block_exchange_right ordinal_two_block_exchange_left.
Qed.

(** Source for [ordinal_suffix_reordering_exists]: an
    actual bijection puts exactly the original
    suffix before the original prefix, supporting
    the sphere identification in 3.4.8(8),
    pp. 329–330. Empty blocks remain. *)
Theorem ordinal_suffix_reordering_exists n m (hMN:(m<=n)%N):
  exists (forward:'I_((n-m)+m)->'I_n) (back:'I_n->'I_((n-m)+m)),
    cancel forward back /\cancel back forward /\
    (forall i:'I_(n-m),forward (lshift m i) = ordinal_coordinate_tail_index hMN i) /\
    (forall i:'I_m,forward (rshift (n-m) i) = widen_ord hMN i).
Proof.
pose hSum:=subnKC hMN.
pose forward:=fun i:'I_((n-m)+m)=>cast_ord hSum (ordinal_two_block_exchange i).
pose back:=fun i:'I_n=>ordinal_two_block_exchange (cast_ord (esym hSum) i).
exists forward,back;split.
- move=>i;by rewrite /forward /back cast_ordK ordinal_two_block_exchange_cancel.
- split.
  + move=>i;by rewrite /forward /back ordinal_two_block_exchange_cancel cast_ordKV.
  + split.
    * move=>i;by rewrite /forward ordinal_two_block_exchange_left.
    * move=>i;rewrite /forward ordinal_two_block_exchange_right;apply:val_inj;by [].
Qed.
