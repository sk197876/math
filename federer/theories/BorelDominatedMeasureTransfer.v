(** Supporting measure comparison for Federer (1969), 2.5.10, p. 101: the
    projected-counting measure is dominated by H^1, and finite H^1
    measurable sets are measurable for it. The proof uses the Borel sandwich
    of 2.2.3, p. 61, not an implication between arbitrary completed sigma
    algebras. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  MeasureCountableClosure BorelRegularMeasureUP BorelRegularSandwich TopologicalBorel
  CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dominated_measure_null]: supporting null
    transfer in the bound of Federer 2.5.10, p. 101,
    directly from the measure laws of 2.1.2, p. 53. *)
Lemma dominated_measure_null (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hn : is_measure nu) :
  (forall A, nu A<=mu A) -> forall A, mu A=0 -> nu A=0.
Proof.
move=> hd A hz; apply/eqP; rewrite eq_le (measure_nonnegative hn) andbT.
by rewrite -hz; exact: hd.
Qed.

(** Source for [borel_dominated_finite_measurable]: supporting
    finite-set transfer for Federer 2.5.10, p. 101,
    using 2.2.3, p. 61, and the null-set law
    2.1.3(6), p. 55. Only the dominating measure
    requires Borel regularity. *)
Lemma borel_dominated_finite_measurable (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hr : is_borel_regular_measure mu) :
  (forall B, borel_set B -> measure_measurable nu B) ->
  (forall B, nu B<=mu B) -> forall A,
  measure_measurable mu A -> mu A < +oo -> measure_measurable nu A.
Proof.
move=> hb hd A hA hf.
have [D [B [hD [hB [hDA [hAB hz]]]]]] := borel_regular_finite_sandwich hm hr hA hf.
have hBD := @dominated_measure_null R X mu nu hn hd (B `\` D) hz.
have hAD : nu (A `\` D)=0.
  apply: (@measure_null_subset R X nu hn (A `\` D) (B `\` D) _ hBD).
  by move=> x [hx hnD]; split=> //; exact: hAB.
have he : A=D `|` (A `\` D).
  apply/seteqP; split=> x.
  - move=> hx; case: (pselect (D x))=> hDx; first by left.
    right; by split.
  - by move=> [hx|[hx _]]; [exact: hDA|].
rewrite he; apply: (@measure_measurable_union R X nu hn D (A `\` D) (hb D hD)).
exact (@measure_null_measurable R X nu hn (A `\` D) hAD).
Qed.

(** Source for [borel_dominated_countably_measurable]: countable
    finite-piece extension of the preceding transfer, using Federer 2.3.4,
    p. 76, and 2.1.3(2), pp. 55–56. *)
Lemma borel_dominated_countably_measurable (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hr : is_borel_regular_measure mu) :
  (forall B, borel_set B -> measure_measurable nu B) ->
  (forall B, nu B<=mu B) -> forall A,
  measure_countably_measurable mu A -> measure_countably_measurable nu A.
Proof.
move=> hb hd A /(countably_measurable_sequence_iff hm) [F [he hF]].
apply/(countably_measurable_sequence_iff hn); exists F; split=> // n; split.
- exact (@borel_dominated_finite_measurable R X mu nu hm hn hr hb hd (F n) (hF n).1 (hF n).2).
- exact: le_lt_trans (hd (F n)) (hF n).2.
Qed.
