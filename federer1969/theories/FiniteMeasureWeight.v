(** Federer (1969), 2.4.16, p. 90: positive coefficients for the weighted
    test. Source context: PositiveIntegrableWeightUP.v. This supporting
    coefficient uses 1+b in the denominator, so null finite-measure pieces
    are retained without division by zero; overlaps in the cover are
    allowed. A summable positive sequence controls both pointwise values and
    integrals. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SequenceSpaceUP SequenceWeights.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_measure_weight]: supporting positive
    coefficient for the countable cover in Federer 2.4.16, p. 90. *)
Definition finite_measure_weight (R : realType) (n : nat) (b : R) :=
  sequence_metric_weight n / (1+b).

(** Source for [finite_measure_weight_bounds]: simultaneous
    positivity, pointwise bound and integral bound of the supporting
    cover coefficients, Federer 2.4.16, p. 90. *)
Lemma finite_measure_weight_bounds (R : realType) (n : nat) (b : R) :
  0 <= b -> 0 < finite_measure_weight n b /\
  finite_measure_weight n b <= sequence_metric_weight n /\
  finite_measure_weight n b * b <= sequence_metric_weight n.
Proof.
move=> hb; have hd : 0 < 1+b := ltr_pwDl ltr01 hb.
have hw := @sequence_metric_weight_positive R n.
split; first by rewrite /finite_measure_weight divr_gt0.
split.
- rewrite /finite_measure_weight ler_pdivrMr // mulrDr mulr1 lerDl.
  exact: mulr_ge0 (ltW hw) hb.
- rewrite /finite_measure_weight mulrAC ler_pdivrMr // mulrDr mulr1 lerDr.
  exact: ltW hw.
Qed.
