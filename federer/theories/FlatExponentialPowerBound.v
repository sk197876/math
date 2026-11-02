(** Federer (1969), 3.1.11, p. 223:
    exp(-x^-2) tends to zero faster than
    any prescribed power as x tends to zero
    through positive values. The estimates follow
    from the sealed addition and tangent laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import RealExponentialUP RealExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ExponentialPower.
Variable R : realType.
Local Notation E := (@RealExponential.exponential R).
Local Notation hE := (@RealExponential.laws R).

(** Source for [real_exponential_natural_multiple]:
    the addition law gives E(n t)=E(t)^n,
    supporting the flat exponential example in
    Federer 3.1.11, p. 223. *)
Lemma real_exponential_natural_multiple n t :
  E (n%:R*t)=(E t)^+n.
Proof.
elim: n=>[|n ih].
- by rewrite mul0r (real_exponential_zero hE) expr0.
- have hn : (n.+1%:R:R)=n%:R+1 by rewrite natr1.
  by rewrite hn mulrDl mul1r (real_exponential_add hE) ih exprS mulrC.
Qed.

(** Source for [real_exponential_negative_inverse]:
    the exponential of -t is the reciprocal
    of the exponential of t, supporting the
    negative exponent in Federer 3.1.11, p. 223. *)
Lemma real_exponential_negative_inverse t : E (-t)=(E t)^-1.
Proof.
have hn : E t!= 0 by rewrite gt_eqF //; exact (real_exponential_positive hE t).
apply: (mulfI hn).
by rewrite -(real_exponential_add hE) ?addNr ?addrN (real_exponential_zero hE) ?mulVf ?mulfV //.
Qed.

(** Source for [real_exponential_power_lower]:
    a degree-n lower bound for the exponential,
    derived by raising the tangent inequality
    at t/n to the nth power. It supports
    flatness in Federer 3.1.11, p. 223. *)
Lemma real_exponential_power_lower n (t : R) :
  (0<n)%N -> 0<=t -> (t/n%:R)^+n<=E t.
Proof.
move=> hn ht.
have hnp : (0:R)<n%:R by rewrite ltr0n.
have hq : 0<=t/n%:R by rewrite divr_ge0 //; exact: ltW hnp.
have htan := real_exponential_tangent hE (t/n%:R).
have hle : t/n%:R<=E (t/n%:R) by lra.
have hb := lerXn2r n hq (ltW (real_exponential_positive hE (t/n%:R))) hle.
have heq : n%:R*(t/n%:R)=t.
  by rewrite mulrC divfK // gt_eqF.
by rewrite -(real_exponential_natural_multiple n (t/n%:R)) heq in hb.
Qed.

(** Source for [real_exponential_negative_power_upper]:
    reciprocal polynomial decay of E(-t),
    supporting the smooth example in Federer
    3.1.11, p. 223. Both denominators
    are strictly positive in the stated hypotheses. *)
Lemma real_exponential_negative_power_upper n (t : R) :
  (0<n)%N -> 0<t -> E (-t)<=(n%:R/t)^+n.
Proof.
move=> hn ht.
have hnp : (0:R)<n%:R by rewrite ltr0n.
have hq : 0<t/n%:R by rewrite divr_gt0.
have hpow : 0<(t/n%:R)^+n := exprn_gt0 _ hq.
have hb := real_exponential_power_lower hn (ltW ht).
have hEpos := real_exponential_positive hE t.
have hinv : (E t)^-1<=((t/n%:R)^+n)^-1.
  by rewrite lef_pV2.
rewrite real_exponential_negative_inverse.
by move: hinv; rewrite -exprVn invfM invrK mulrC.
Qed.

(** Source for [flat_exponential_power_bound]:
    for every positive n, exp(-x^-2) is
    at most n^n x^(2n) when x>0.
    This bound proves the vanishing derivative
    limits needed in Federer 3.1.11, p. 223,
    without importing a series or calculus theorem. *)
Lemma flat_exponential_power_bound n (x : R) :
  (0<n)%N -> 0<x ->
  E (-((x^-1)^+2))<=n%:R^+n*x^+(2*n).
Proof.
move=> hn hx.
have hi : 0<x^-1 by rewrite invr_gt0.
have ht : 0<(x^-1)^+2 := exprn_gt0 _ hi.
have hb := real_exponential_negative_power_upper hn ht.
by rewrite -exprVn invrK exprMn -exprM in hb.
Qed.
End ExponentialPower.
