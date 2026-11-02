(** Federer (1969), 2.2.3, p. 61, Borel sandwich: supporting
    finite-measurable-set transfer for the restricted weighted measure in
    2.10.24, p. 188. It suffices that the second measure has measurable
    Borel sets and vanishes on null sets of the Borel regular measure. No
    quantitative domination is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureFiniteClosure
  BorelRegularMeasureUP BorelRegularSandwich TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [borel_null_transfer_finite_measurable]: supporting
    transfer of finite-measure measurability for the final
    paragraph of 2.10.24, p. 188, by the Borel
    sandwich in 2.2.3, p. 61, and null-set
    measurability 2.1.3(6), p. 55. Only null-set
    preservation is imposed on the second measure. *)
Lemma borel_null_transfer_finite_measurable (R : realType) (X : topologicalType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (hr : is_borel_regular_measure mu) :
  (forall B, borel_set B -> measure_measurable nu B) ->
  (forall B, mu B=0 -> nu B=0) -> forall A,
  measure_measurable mu A -> mu A< +oo -> measure_measurable nu A.
Proof.
move=> hb hnull A hA hfin.
have [D [B [hD [hB [hDA [hAB hz]]]]]] := borel_regular_finite_sandwich hm hr hA hfin.
have hBD := hnull (B `\` D) hz.
have hAD : nu (A `\` D)=0.
  apply: (@measure_null_subset R X nu hn (A `\` D) (B `\` D) _ hBD).
  by move=> x [hx hxD]; split=> //; exact: hAB.
have he : A=D `|` (A `\` D).
  apply/seteqP; split=> x.
  - move=> hx; case: (pselect (D x))=> hxD; first by left.
    right; by split.
  - by move=> [hx|[hx _]]; [exact: hDA|].
rewrite he; apply: (@measure_measurable_union R X nu hn D (A `\` D) (hb D hD)).
exact: (@measure_null_measurable R X nu hn (A `\` D) hAD).
Qed.
