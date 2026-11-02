(** Federer (1969), 2.5.1–2.5.2, pp. 91–92: the closure-only lattice
    definition permits the empty lattice, whose representation assertion is
    vacuous. We record why this split is needed: the infimum over suiting
    sequences of an empty lattice is infinite even on the empty set, whereas
    the zero measure gives the required vacuous representation. This is a
    boundary clarification, not a correction listed in Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellCoverUP MeasureUP MeasureBasic NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_empty_envelope_infinite]: Supporting Federer 2.5.2,
    p. 92.This statement concerns the envelope formula, not the measure
    promised by the representation theorem for an empty lattice. *)
Lemma daniell_empty_envelope_infinite (R : realType) (X : Type)
    (A : (X -> R) -> R) (mu : set X -> \bar R) :
  is_daniell_cover_envelope set0 A mu -> forall S, mu S=+oo.
Proof.
move=> hm S; apply/eqP; rewrite eq_le leey /=.
apply: (daniell_cover_greatest hm)=> f c hs hc; exfalso; exact: (hs.1 0%N).1.
Qed.

(** Source for [daniell_empty_envelope_not_measure]: Supporting Federer
    2.5.2, p. 92.The proof uses the previously established empty-set measure
    law. *)
Lemma daniell_empty_envelope_not_measure (R : realType) (X : choiceType)
    (A : (X -> R) -> R) (mu : set X -> \bar R) :
  is_daniell_cover_envelope set0 A mu -> ~ is_measure mu.
Proof.
move=> he hm; have hh := daniell_empty_envelope_infinite he set0.
by rewrite (measure_empty hm) in hh.
Qed.

(** Source for [daniell_zero_measure]: the zero-measure witness for the
    empty lattice in Federer 2.5.2, p. 92 The measure laws are proved
    directly from the project's definition in 2.1.2. *)
Lemma daniell_zero_measure (R : realType) (X : choiceType) :
  is_measure (fun _ : set X => (0 : \bar R)).
Proof.
constructor; first by move=> S.
move=> T F hF hT; exact: nonnegative_sum_nonnegative.
Qed.
