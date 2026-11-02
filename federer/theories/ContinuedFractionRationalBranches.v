(** Federer (1969), 2.2.9, p. 65, supporting rationality calculation for
    inverse continued-fraction steps. Bell2016, section 1, p. 1, states
    invariance of irrationality under the Gauss map. We prove the required
    elementary integer-ratio direction directly. Source context:
    ContinuedFractionBranches.v and RationalRealUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RationalRealUP ContinuedFractionBranches.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_branch_quotient]: supporting
    rational inverse-step identity for Federer 2.2.9, p. 65:
    applying digit a+1 to p/q gives q/((a+1)q+p). *)
Lemma continued_fraction_branch_quotient (R : realType) a p q :
  (0 < q)%N -> continued_fraction_branch a ((p%:R : R)/q%:R) =
    q%:R / ((a.+1*q+p)%:R).
Proof.
move=> hq; have hq0 : (q%:R : R) != 0 by rewrite pnatr_eq0 -lt0n.
rewrite /continued_fraction_branch natrD natrM.
have he : a.+1%:R + (p%:R : R)/q%:R = (a.+1%:R*q%:R+p%:R)/q%:R.
  by rewrite mulrDl mulfK.
by rewrite he invf_div.
Qed.

(** Source for [continued_fraction_branch_rational]: supporting
    rationality of the inverse step in Federer 2.2.9,
    p. 65. This proves the contrapositive needed to
    continue an irrational point's Gauss digits. *)
Lemma continued_fraction_branch_rational (R : realType) a (t : R) :
  0 < t -> is_rational_real t -> is_rational_real (continued_fraction_branch a t).
Proof.
move=> ht hr; have [p [q [hp [hq ->]]]] := positive_rational_natural_quotient ht hr.
rewrite continued_fraction_branch_quotient //.
apply: natural_quotient_rational.
by rewrite addn_gt0 muln_gt0 ltn0Sn hq.
Qed.

(** Source for [continued_fraction_zero_tail_rational]: supporting
    rational endpoint exception for the classical map in Federer
    2.2.9, p. 65. A zero remainder gives the
    rational number one divided by the first positive digit. *)
Lemma continued_fraction_zero_tail_rational (R : realType) a :
  is_rational_real (@continued_fraction_branch R a 0).
Proof.
rewrite /continued_fraction_branch addr0 -div1r.
exact: (@natural_quotient_rational R 1 a.+1 (ltn0Sn a)).
Qed.
