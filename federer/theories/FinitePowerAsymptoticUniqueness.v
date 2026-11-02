(** Federer (1969), 3.1.11, p. 221:
    two finite polynomial expansions with the same
    order-k remainder have identical coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormLittleOPower VectorPolynomialLittleOUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_power_asymptotic_coefficients_unique]:
    the linewise polynomial comparison in Federer
    3.1.11, p. 221. Both
    expansions are compared with the same function;
    subtracting the remainders gives a negligible
    polynomial, whose coefficients must vanish. *)
Theorem finite_power_asymptotic_coefficients_unique (R : realType)
    (Y : lmodType R) (N : Y->R) (hN : is_real_norm N)
    k M (f : R->Y) (c d : nat->Y) :
  (M<=k.+1)%N ->
  norm_little_o_power N (fun t=>f t-\sum_(i<M) t^+i*:c i) k ->
  norm_little_o_power N (fun t=>f t-\sum_(i<M) t^+i*:d i) k ->
  forall i, (i<M)%N -> c i=d i.
Proof.
move=>hMk hc hd.
have hh := norm_little_o_power_add hN hd (norm_little_o_power_negate hN hc).
have he t :
    (f t-\sum_(i<M) t^+i*:d i) + -(f t-\sum_(i<M) t^+i*:c i)=
    \sum_(i<M) t^+i*:(c i-d i).
  rewrite opprB [(_-f t)]addrC addrACA subrr add0r addrC -sumrB.
  apply: eq_bigr=>i _; by rewrite scalerBr.
have hp : norm_little_o_power N (fun t=>\sum_(i<M) t^+i*:(c i-d i)) k.
  move=>e heps; have [r [hr hb]] := hh e heps.
  exists r; split=> // t ht; rewrite -(he t); exact: hb.
move=>i hi; have hz := @finite_power_little_o_coefficients_zero R Y N hN k M
  (fun j=>c j-d j) hMk hp i hi.
by move/eqP:hz; rewrite subr_eq0=>/eqP.
Qed.
