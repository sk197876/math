(** Supporting exhaustion argument for corrected associativity in Federer
    (1969), 2.6.5, p. 119, as stated with countable measurability.
    Finite-mass cylinder bounds extend to arbitrary measurable first
    factors. The only extra case is a zero second factor, where a countable
    union of null cylinders is null. This uses Federer's 2.1.2, p. 53, and
    2.3.4, p. 76. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic
  CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_cylinder_bound]: supporting passage
    from finite to countably measurable factors for corrected Federer 2.6.5,
    p. 119 (. Neither E nor the map f needs measurability: the asserted
    finite cylinder bounds supply the needed control. *)
Lemma countably_measurable_cylinder_bound (R : realType) (X M : choiceType)
    (alpha : set X -> \bar R) (mu : set M -> \bar R)
    (ha : is_measure alpha) (hm : is_measure mu)
    (f : M -> X) (E : set M) (b : \bar R) :
  measure_countably_measurable alpha setT -> 0 <= b ->
  (forall A, measure_measurable alpha A -> alpha A < +oo ->
    mu ((f @^-1` A) `&` E) <= alpha A * b) ->
  forall A, measure_measurable alpha A -> mu ((f @^-1` A) `&` E) <= alpha A * b.
Proof.
move=> hX hb hfin A hA.
case: (ltP (alpha A) +oo)=> hAf; first exact: hfin hA hAf.
have haInf : alpha A = +oo by apply/eqP; rewrite eq_le leey hAf.
have [hb0|hbn] := eqVneq b 0.
- subst b; rewrite mule0.
  have [F [hcover hF]] := (proj1 (@countably_measurable_sequence_iff R X alpha ha setT)) hX.
  have hn n : mu ((f @^-1` F n) `&` E) = 0.
    have h := hfin (F n) (hF n).1 (hF n).2.
    rewrite mule0 in h; apply/eqP; rewrite eq_le h /=; exact (measure_nonnegative hm _).
  have hU := @measure_null_countable_union R M nat mu hm setT
    (fun n => (f @^-1` F n) `&` E) (countableP _) (fun n _ => hn n).
  have hsub : (f @^-1` A) `&` E `<=` \bigcup_n ((f @^-1` F n) `&` E).
    move=> p [_ hp].
    have hx : (\bigcup_n F n) (f p) by rewrite -hcover.
    have [n _ hnx] := hx; exists n=> //; by split.
  have he := measure_null_subset hm hsub hU; by rewrite he.
- have hbp : 0 < b by rewrite lt_def hbn hb.
  by rewrite haInf gt0_mulye // leey.
Qed.
