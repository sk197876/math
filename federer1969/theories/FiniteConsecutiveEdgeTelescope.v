(** Federer (1969), 4.1.27, p. 384:
    summation by parts converts the original
    consecutive-edge expression into barycentric coefficients.
    This finite additive identity uses the
    existing vector and scalar operations only. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_consecutive_edge_telescope]: the elementary
    finite rearrangement implicit in the positive
    barycentric image display of 4.1.27, p. 384.
    No coefficient sign or independence is assumed. *)
Theorem finite_consecutive_edge_telescope (K:fieldType) (V:lmodType K)
    (p:nat->K) (v:nat->V) m:
  p 0%N*:v 0%N+\sum_(i<m) p i.+1*:(v i.+1-v i)=
    \sum_(i<m) (p i-p i.+1)*:v i+p m*:v m.
Proof.
elim:m=>[|m ih];first by rewrite !big_ord0 addr0 add0r.
rewrite !big_ord_recr /= addrA ih scalerBr scalerBl.
by rewrite -!addrA [p m.+1*:v m.+1-p m.+1*:v m]addrC.
Qed.
