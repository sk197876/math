(** Federer (1969), 3.4.8(4),(6), pp. 326, 328:
    finite index bookkeeping for the original basis
    vectors e_i with i>j. Indices are zero based. *)
From mathcomp Require Import all_boot all_order.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [ordinal_coordinate_tail_index]: enumerate
    exactly the basis indices outside the first p,
    supporting 3.4.8(4), p. 326. *)
Definition ordinal_coordinate_tail_index n p (hPN:(p<=n)%N) (i:'I_(n-p)):'I_n:=
  cast_ord (subnKC hPN) (rshift p i).

(** Source for [ordinal_coordinate_tail_value]: the i-th
    tail index has value p+i, supporting the
    original fixed-frame equation, 3.4.8(4), p. 326. *)
Lemma ordinal_coordinate_tail_value n p (hPN:(p<=n)%N) (i:'I_(n-p)):
  (ordinal_coordinate_tail_index hPN i:nat) = (p+i)%N.
Proof. by []. Qed.

(** Source for [ordinal_coordinate_tail_injective]: tail
    indices are distinct, supporting the orthonormal
    fixed frame in 3.4.8(6), p. 328. *)
Lemma ordinal_coordinate_tail_injective n p (hPN:(p<=n)%N):
  injective (@ordinal_coordinate_tail_index n p hPN).
Proof.
move=>i j hEqual.
have hValues:(p+i)%N = (p+j)%N:=congr1 (fun t:'I_n=>(t:nat)) hEqual.
have hIJ:(i:nat) = (j:nat):=@addnI p i j hValues.
exact:val_inj hIJ.
Qed.

(** Source for [ordinal_coordinate_tail_complete]: every
    original basis index at least p occurs in
    the fixed tail, supporting 3.4.8(4), p. 326. *)
Lemma ordinal_coordinate_tail_complete n p (hPN:(p<=n)%N) (i:'I_n):
  (p<=i)%N ->exists j,ordinal_coordinate_tail_index hPN j = i.
Proof.
move=>hPI.
have hBound:(i-p<n-p)%N by rewrite (@ltn_sub2rE p i n hPI);exact:ltn_ord.
exists (Ordinal hBound);apply:val_inj.
change ((p+(i-p))%N = (i:nat)).
exact:(subnKC hPI).
Qed.
