(** Federer (1969), 4.1.27, p. 384:
    multiplying the differential's diagonal prefixes
    gives x_1^(m-1) ... x_(m-1).
    This finite product identity keeps zero factors
    and the empty products; no coordinate
    is divided out. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_prefix_product_power]: the elementary
    exponent count in the original wedge
    differential formula of 4.1.27, p. 384.
    Its commutative-ring form includes all original
    real and degree-zero cases. *)
Theorem finite_prefix_product_power (K:comNzRingType) (x:nat->K) m:
  (\prod_(i<m) \prod_(j<i) x j)=
    \prod_(i<m) (x i)^+(m-(val i).+1).
Proof.
elim:m=>[|m ih];first by rewrite !big_ord0.
rewrite big_ord_recr /= ih [RHS]big_ord_recr /= subnn expr0 mulr1.
rewrite -big_split.
apply:eq_bigr=>i _.
have hExponent:(m-val i)%N=(m-(val i).+1).+1.
  by rewrite (subnSK (ltn_ord i)).
by rewrite subSS hExponent exprS mulrC.
Qed.
