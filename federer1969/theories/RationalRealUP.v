(** Supporting scalar definition for Federer (1969), 2.2.9, p. 65, the set
    of irrational numbers between zero and one. Rationality means being a
    ratio of an integer and a positive natural denominator in the existing
    real field. No computable real or continued-fraction representation is
    used to define rationality. Bell2016, section 1, p. 1, uses this same
    rational/irrational distinction *)
From mathcomp Require Import all_boot all_order all_algebra ssrint reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_rational_real]: supporting ordinary rational
    scalar predicate for the irrational target in Federer 2.2.9,
    p. 65, stated by integer-ratio existence rather
    than by continued-fraction termination. *)
Definition is_rational_real (R : realType) (x : R) : Prop :=
  exists p : int, exists q : nat, (0 < q)%N /\ x = p%:~R / q%:R.
Arguments is_rational_real {R} x.

(** Source for [irrational_unit_interval]: direct target set
    of the classical homeomorphism mentioned in Federer 2.2.9,
    p. 65: irrational real numbers strictly between
    zero and one. Irrationality is the negation of ordinary
    integer-ratio rationality, not a property of a coding. *)
Definition irrational_unit_interval (R : realType) (x : R) : Prop :=
  0 < x /\ x < 1 /\ ~ is_rational_real x.
Arguments irrational_unit_interval {R} x.

(** Source for [natural_quotient_rational]: elementary scalar
    support for the rational endpoints of the continued-fraction
    cylinders in Federer 2.2.9, p. 65. *)
Lemma natural_quotient_rational (R : realType) p q :
  (0 < q)%N -> is_rational_real ((p%:R : R) / q%:R).
Proof. move=> hq; exists (Posz p),q; by split. Qed.

(** Source for [positive_rational_natural_quotient]: supporting
    positive numerator and denominator form for the rational
    exclusion argument in Federer 2.2.9, p. 65.
    Positivity rules out a negative or zero integer numerator. *)
Lemma positive_rational_natural_quotient (R : realType) (x : R) :
  0 < x -> is_rational_real x ->
  exists p q : nat, (0 < p)%N /\ (0 < q)%N /\ x = p%:R / q%:R.
Proof.
move=> hx [p [q [hq he]]].
have hqR : (0 : R) < q%:R by rewrite ltr0n.
have hp : (0 : R) < p%:~R.
  by move: hx; rewrite he ltr_pdivlMr // mul0r.
case: p he hp=> [p|p] he hp.
- exists p,q; split; first by move: hp; rewrite ltr0n.
  by split.
- by move: hp; rewrite /= ltrNr oppr0 ltrn0.
Qed.
