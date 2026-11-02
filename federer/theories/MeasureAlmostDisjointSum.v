(** Federer (1969), 3.2.23, p. 260: sum over a countable
    disjoint measurable family covering all but a null remainder.
    This supporting measure identity is the countable additivity
    law of 2.1.3(3), p. 55, with the omitted set retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic MeasureSplit MeasureCountableAdditivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_almost_disjoint_cover_sum]: supporting
    countable image decomposition in Federer 3.2.23, p. 260.
    Infinite total mass is permitted, the enclosing set need not
    be measurable, and a null omitted remainder is not silently
    replaced by an exact covering hypothesis. *)
Theorem measure_almost_disjoint_cover_sum (R:realType) (X I:choiceType)
    (rho:set X->\bar R) (hr:is_measure rho) (A:set X) (D:set I) (P:I->set X):
  countable D ->(forall i,D i ->P i `<=` A) ->
  (forall i j,D i ->D j ->i!=j ->forall x,P i x ->P j x ->False) ->
  (forall i,D i ->measure_measurable rho (P i)) ->
  rho (A `\` (\bigcup_(i in D) P i))=0 ->
  rho A=nonnegative_sum D (fun i=>rho (P i)).
Proof.
move=>hCount hSub hDisjoint hMeas hNull.
pose U:=\bigcup_(i in D) P i.
have hUA:U `<=` A by move=>x [i hi hx]; exact:(hSub i hi x hx).
have hCover:A `<=` U `|` (A `\` U).
  move=>x hx; have [hU|hU]:=pselect (U x); [by left|right; by split].
have hUpper:=measure_binary_cover hr hCover.
rewrite hNull adde0 in hUpper.
have hValue:rho A=rho U by apply/eqP; rewrite eq_le hUpper (measure_mono hr hUA).
rewrite hValue.
exact:(measure_countable_disjoint_additivity hr hCount hMeas hDisjoint).
Qed.
