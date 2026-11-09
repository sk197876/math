(** Federer (1969), 3.4.5, p. 321: the
    actual even and odd y coefficient shifts in the
    quadratic remainder of the cited analytic example. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [paired_parity_coefficient_shift]: a quadratic
    y shift is a single paired-index shift in
    each original parity, including both initial coefficients,
    supporting 3.4.5, p. 321. *)
Theorem paired_parity_coefficient_shift (V:zmodType) (b:nat->V) (parity k:nat):
  (parity=0%N \/parity= 1%N) ->
  (if (2<=2*k+parity)%N then b (2*k+parity-2)%N else 0)=
    if (1<=k)%N then b (2*(k-1)+parity)%N else 0.
Proof.
move=>hParity;case:k=>[|k].
- by case:hParity=>[->|->].
- rewrite mulnS [((2+2*k)+parity)%N]addnAC subn1 /=.
  by rewrite -addnA addKn addnC.
Qed.
