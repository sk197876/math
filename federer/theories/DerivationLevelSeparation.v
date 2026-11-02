(** Full numerical-level separation for Federer (1969), 2.9.6, p. 155. The
    existing criterion 2.3.2(7), pp. 74–75, uses closed levels. Enlarge them
    to strict levels at two positive intermediate thresholds before applying
    Federer's bounded Borel hull argument. Negative lower levels are empty
    by nonnegativity of defined derivates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureDerivationContext MeasureDerivates
  PartialFunctionUP CoveringRelationLimits DerivationRatioDomain DerivationRationalGaps
  ExtendedRealOrderTopology DerivationHullSeparation BoundedPartitionSeparation
  MeasurableSeparationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_derivate_value_nonnegative]: supporting
    sign reduction for numerical separation in Federer 2.9.6,
    p. 155, with the sign convention of 2.9.5,
    p. 154. Every defined derivate is nonnegative,
    including at points outside the conull existence set. *)
Lemma measure_derivate_value_nonnegative (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) x y :
  is_measure phi -> is_measure psi ->
  partial_function_graph (measure_derivate psi phi V) x y -> 0<=y.
Proof.
move=> hf hp [_ [_ hl]].
have h := @measure_ratio_lower_limit_nonnegative R X psi phi V x hp hf.
by rewrite hl in h.
Qed.

(** Source for [measure_derivate_level_separated]: the full separation
    criterion used in Federer 2.9.6, p. 155 Closed levels at arbitrary
    finite a<b are enlarged to strict positive levels, and bounded Borel
    localisation is removed by countable additivity on restrictions. *)
Lemma measure_derivate_level_separated (R : realType) (X : metricType R)
    (phi psi : set X -> \bar R) (V : X -> set X -> Prop) :
  is_measure_derivation_context phi V -> is_derivation_measure psi ->
  is_measure_level_separated phi (measure_derivate psi phi V).
Proof.
move=> hc hp T a b hab.
have hf := derivation_context_measure hc.
have hm := derivation_measure_law hf.
pose f := measure_derivate psi phi V.
pose A := T `&` partial_function_preimage f [set y | y<=a%:E].
pose B := T `&` partial_function_preimage f [set y | b%:E<=y].
change (phi A+phi B<=phi T).
case: (pselect (0<b)%R)=> hb.
- have hmax0 : (0<=Num.max a 0)%R by rewrite le_max lexx orbT.
  have hmaxb : (Num.max a 0<b)%R by rewrite gt_max hab hb.
  have hmax0E : 0<=(Num.max a 0)%:E by rewrite lee_fin.
  have hmaxbE : (Num.max a 0)%:E<b%:E by rewrite lte_fin.
  have [p [[hc0 hcd] [hmaxc hdb]]] := @positive_rational_gap_between R
    (Num.max a 0)%:E b%:E hmax0E hmaxbE.
  have hac : a%:E<(ratr p.1 : R)%:E.
    apply: le_lt_trans _ hmaxc; by rewrite lee_fin le_max lexx.
  apply: (@measure_separation_from_bounded_cells R X phi A B T hm (derivation_measure_borel_regular hf))=> K hK hKb.
  have hsep : phi (A `&` K)+phi (B `&` K)<=phi ((A `&` K) `|` (B `&` K)).
    apply: (@derivation_bounded_strict_separation R X phi psi V K (A `&` K) (B `&` K)
      (ratr p.1 : R) (ratr p.2 : R) hc hp hK hKb (fun x hx => hx.2) (fun x hx => hx.2) hc0 hcd).
    + move=> x [[_ [y [hy hya]]] _]; exists y; split=> //; exact: le_lt_trans hya hac.
    + move=> x [[_ [y [hy hby]]] _]; exists y; split=> //; exact: lt_le_trans hdb hby.
  apply: le_trans hsep _; apply: (@measure_mono R X phi hm)=> x [[[ht _] hk]|[[ht _] hk]]; by split.
- have hb0 : (b<=0)%R by rewrite leNgt; exact/negP.
  have ha0 : (a<0)%R := lt_le_trans hab hb0.
  have hA0 : A=set0.
    apply/seteqP; split=> [x [_ [y [hy hya]]]|x []].
    have hy0 := @measure_derivate_value_nonnegative R X phi psi V x y hm (derivation_measure_law hp) hy.
    have ha0E : a%:E<0 by rewrite lte_fin.
    by have := le_lt_trans (le_trans hy0 hya) ha0E; rewrite ltxx.
  rewrite hA0 (measure_empty hm) add0e.
  apply: (@measure_mono R X phi hm)=> x [hx _]; exact hx.
Qed.
