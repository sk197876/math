(** Federer (1969), 2.2.9, p. 65, final comparison with the classical
    continued-fraction homeomorphism. These finite expression operations
    support the displayed continued fraction; the infinite limit map will be
    specified separately. Natural digit a denotes the positive integer a+1,
    as in the project's 2.2.6 coordinate convention. Additional local
    reference: Jordan Bell, Measure theory and Perron-Frobenius operators
    for continued fractions, 18 April 2016, section 1, p. 1, for the inverse
    branches, and Theorem 2, p. 5, for the interval cylinders. Federer cites
    O. Perron, Irrationalzahlen (Chelsea, 1948), p. 103; that original
    passage has not been consulted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continued_fraction_branch]: finite inverse
    branch t maps to 1/(a+1+t) of the displayed
    fraction in Federer 2.2.9, p. 65. Bell2016,
    section 1, p. 1, defines the Gauss step; the
    displayed branch inverts one of its digit intervals. *)
Definition continued_fraction_branch (R : realType) (a : nat) (t : R) : R :=
  ((a.+1)%:R + t)^-1.

(** Source for [continued_fraction_denominator_positive]: supporting
    nonvanishing denominator for the positive-digit fractions in
    Federer 2.2.9, p. 65, with nonnegative tails. *)
Lemma continued_fraction_denominator_positive (R : realType) a (t : R) :
  0 <= t -> 0 < (a.+1)%:R + t.
Proof.
move=> ht; have ha : (0 : R) < a.+1%:R by rewrite ltr0n.
apply: lt_le_trans ha _; by rewrite lerDl.
Qed.

(** Source for [continued_fraction_branch_unit_bounds]: supporting
    unit-interval bounds for the finite fractions in Federer
    2.2.9, p. 65. Every nonnegative tail gives
    a value strictly positive and at most one. *)
Lemma continued_fraction_branch_unit_bounds (R : realType) a (t : R) :
  0 <= t -> 0 < continued_fraction_branch a t /\ continued_fraction_branch a t <= 1.
Proof.
move=> ht; have hp := @continued_fraction_denominator_positive R a t ht.
rewrite /continued_fraction_branch; split; first by rewrite invr_gt0.
rewrite invf_le1 //.
have ha : (1 : R) <= a.+1%:R by rewrite ler1n.
have hh := lerD ha ht; by rewrite addr0 in hh.
Qed.

(** Source for [continued_fraction_branch_positive_tail]: supporting
    strict upper bound in Federer 2.2.9, p. 65.
    A strictly positive tail prevents the endpoint one even
    when the leading digit is one. *)
Lemma continued_fraction_branch_positive_tail (R : realType) a (t : R) :
  0 < t -> continued_fraction_branch a t < 1.
Proof.
move=> ht; rewrite /continued_fraction_branch invf_lt1;
  last exact: (@continued_fraction_denominator_positive R a t (ltW ht)).
have ha : (1 : R) <= a.+1%:R by rewrite ler1n.
have hh := ler_ltD ha ht; by rewrite addr0 in hh.
Qed.

(** Source for [continued_fraction_branch_reciprocal]: supporting
    inverse-branch identity for the classical fraction in Federer
    2.2.9, p. 65. It recovers the digit plus
    tail from the reciprocal of the branch value. *)
Lemma continued_fraction_branch_reciprocal (R : realType) a (t : R) :
  (continued_fraction_branch a t)^-1 = (a.+1)%:R + t.
Proof. by rewrite /continued_fraction_branch invrK. Qed.

(** Source for [continued_fraction_branch_decreasing]: supporting
    strict reversal of order by an inverse branch in Federer
    2.2.9, p. 65, used to identify its open
    interval image as in Bell2016 Theorem 2, p. 5. *)
Lemma continued_fraction_branch_decreasing (R : realType) a (s t : R) :
  0 <= s -> s < t -> continued_fraction_branch a t < continued_fraction_branch a s.
Proof.
move=> hs hst.
have hp := @continued_fraction_denominator_positive R a s hs.
have hq := @continued_fraction_denominator_positive R a t (le_trans hs (ltW hst)).
by rewrite /continued_fraction_branch (@ltf_pV2 R _ _ hq hp) ltrD2l.
Qed.
