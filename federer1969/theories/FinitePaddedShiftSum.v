(** Federer (1969), 3.4.5, p. 321: finite
    coefficient shifts with exact zero padding, supporting
    the quadratic remainder cancellation in the cited example. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_padded_shift_sum]: shifting an
    original finite coefficient family can be transferred to
    a weight vanishing beyond the same finite cutoff,
    supporting 3.4.5, p. 321. All cutoffs and
    shifts, including empty ranges, are retained. *)
Theorem finite_padded_shift_sum (K:comPzRingType) (N d:nat) (a w:nat->K):
  (forall i,(N<=i)%N ->w i=0) ->
  (\sum_(i<N) (if (d<=i)%N then a (i-d)%N else 0)*w i)=
    \sum_(i<N) a i*w (i+d)%N.
Proof.
move=>hSupport.
have hToNat:(\sum_(i<N) (if (d<=i)%N then a (i-d)%N else 0)*w i)=
    \sum_(d<=i<N) a (i-d)%N*w i.
  rewrite big_geq_mkord /= [RHS]big_mkcond.
  apply:eq_bigr=>i _;by case:(d<=i)%N;rewrite ?mul0r.
have hShift:(\sum_(d<=i<N) a (i-d)%N*w i)=\sum_(i<N-d) a i*w (i+d)%N.
  rewrite -(add0n d) big_addn add0n big_mkord.
  by apply:eq_bigr=>i _;rewrite addnK.
rewrite hToNat hShift (big_ord_widen N (fun i=>a i*w (i+d)%N) (leq_subr d N)) big_mkcond.
apply:eq_bigr=>i _;case hI:(i<N-d)%N;first by [].
have hAtLeast:(N-d<=i)%N by rewrite leqNgt hI.
have hIndex:(N<=i+d)%N by rewrite addnC -leq_subLR.
by rewrite (hSupport (i+d)%N hIndex) mulr0.
Qed.
