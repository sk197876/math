(** Federer (1969), 2.6.2(3), pp. 115, 117: extend the finite measurable-set
    formula to a countably measurable set by disjoint decomposition. No
    sigma-finiteness of either ambient factor is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasureCountableClosure MeasureCountableAdditivity
  SetSequenceDisjointification MeasureSequencePrefixes CountablyMeasurableUP CountablyMeasurableSequences
  MeasureIntegralUP MeasureIntegralAlmostEquality TotalNonnegativeSeriesIntegral NonnegativeSum
  ProductMeasure ProductSections FiniteProductSetFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_countably_measurable_vertical_fubini]: direct
    first-coordinate outer-integral form of Federer 2.6.2(3), p. 115,
    completed in the proof on p. 117 The countable-measurability hypothesis
    is retained exactly. *)
Theorem product_countably_measurable_vertical_fubini (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  measure_countably_measurable (product_measure ha hb) S ->
  measure_almost_everywhere alpha [set x | measure_measurable beta (product_vertical_section S x)] /\
  is_measure_integral alpha (partial_function_total (fun x => beta (product_vertical_section S x)))
    (product_measure ha hb S).
Proof.
move=> hS; pose nu := product_measure ha hb; have hnu := product_measure_is_measure ha hb.
have [F [he hF]] := (countably_measurable_sequence_iff hnu S).1 hS.
pose D := set_sequence_disjointify F.
have hDm n : measure_measurable nu (D n).
  apply: (@measure_sequence_disjointify_measurable R (X * Y)%type nu hnu F)=> k; exact: (hF k).1.
have hDf n : nu (D n) < +oo.
  apply: le_lt_trans _ (hF n).2; apply: (@measure_mono R (X * Y)%type nu hnu (D n) (F n)).
  by move=> z [hz _].
have hDd n m : n != m -> forall z, D n z -> D m z -> False.
  exact: set_sequence_disjointify_disjoint.
have hDU : S = \bigcup_n D n by rewrite /D set_sequence_disjointify_union.
have hfi n := @product_finite_vertical_fubini R X Y alpha beta ha hb (D n) (hDm n) (hDf n).
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)]
  alpha ha setT (fun n => [set x | measure_measurable beta (product_vertical_section (D n) x)])
  (countableP setT) (fun n _ => (hfi n).1).
pose u n x : extended_real_line R := beta (product_vertical_section (D n) x).
have hpoint x : (forall n, measure_measurable beta (product_vertical_section (D n) x)) ->
    beta (product_vertical_section S x) = nonnegative_sum setT (fun n => u n x).
  move=> hm; rewrite hDU product_vertical_union.
  apply: (@measure_sequence_disjoint_additivity R Y beta hb _ hm)=> n m hne y hn hm'.
  exact: (hDd n m hne (x,y) hn hm').
split.
- apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ hall)=> x hx.
  change (measure_measurable beta (product_vertical_section S x)).
  rewrite hDU product_vertical_union; apply: (measure_measurable_sequence_union hb)=> n.
  exact: hx n I.
- have hi := @total_nonnegative_series_integral R X alpha ha u (fun n => nu (D n))
    (fun n x => measure_nonnegative hb _) (fun n => (hfi n).2).
  have hsum : nu S = nonnegative_sum setT (fun n => nu (D n)).
    rewrite hDU; exact: (@measure_sequence_disjoint_additivity R (X * Y)%type nu hnu D hDm hDd).
  rewrite -hsum in hi; apply: (@measure_integral_almost_equal R X alpha ha _ _ _ hi).
  apply: (@measure_almost_everywhere_mono R X alpha ha _ _ _ hall)=> x hx.
  exists (beta (product_vertical_section S x)); split=> //.
  exact: esym (hpoint x (fun n => hx n I)).
Qed.
