(** Federer (1969), 2.5.6, p. 98: the names variation integral and variation
    measure for the sums of the positive and negative parts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP NonnegativeSumAdd.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [variation_integral]: direct naming convention
    mu+ + mu- in Federer 2.5.6, p. 98. The two
    real-valued functionals are specified and obtained in 2.5.5;
    this definition names their sum without choosing new witnesses. *)
Definition variation_integral (R : realType) (X : Type)
    (P Q : (X -> R) -> R) (f : X -> R) := (P f+Q f)%R.

(** Source for [variation_measure]: direct naming convention
    psi+ + psi- in Federer 2.5.6, p. 98. Each measure
    is defined on all subsets, and infinite values are allowed. *)
Definition variation_measure (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (S : set X) := mu S+nu S.

(** Source for [variation_measure_laws]: verification that
    the sum called a measure in Federer 2.5.6, p. 98,
    satisfies his definition 2.1.2, p. 53. This supporting
    proof uses nonnegative summation 2.1.1(4), p. 52. *)
Lemma variation_measure_laws (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) :
  is_measure mu -> is_measure nu -> is_measure (variation_measure mu nu).
Proof.
move=> hm hn; constructor.
- move=> S; exact: adde_ge0 (measure_nonnegative hm S) (measure_nonnegative hn S).
- move=> S F hF hcover; rewrite /variation_measure nonnegative_sum_add.
  + exact: leeD (@measure_countable_cover R X mu hm S F hF hcover)
      (@measure_countable_cover R X nu hn S F hF hcover).
  + move=> T _; exact: measure_nonnegative hm T.
  + move=> T _; exact: measure_nonnegative hn T.
Qed.

(** Source for [variation_measure_common_measurable]: supporting
    measurability law for the sum named in Federer 2.5.6, p. 98.
    It follows directly from the splitting definition 2.1.2, p. 54;
    no equality of the two complete measurable families is asserted. *)
Lemma variation_measure_common_measurable (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) S :
  measure_measurable mu S -> measure_measurable nu S ->
  measure_measurable (variation_measure mu nu) S.
Proof.
move=> hm hn T; rewrite /variation_measure (hm T) (hn T).
by rewrite addeACA.
Qed.
