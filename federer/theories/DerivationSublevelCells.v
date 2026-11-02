(** Bounded auxiliary cells in Federer (1969), 2.9.3, p. 154. The strict
    ratio subrelation is refined by diameter less than one, without changing
    fineness. This makes numerator and denominator finite under the original
    class M. A defined ratio excludes zero denominators. its non-strict
    lower-limit premise differs from Federer's. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext MeasureUP MeasureBasic
  CoveringLowerSublevel MeasureDerivates MeasureRatioComparison PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_sublevel_cell_bound]: supporting
    cellwise inequality in Federer 2.9.3, p. 154:
    alpha(S)<=c beta(S). The diameter cutoff is an
    auxiliary proof refinement; the theorem has no new
    boundedness assumption on its target set. *)
Lemma derivation_sublevel_cell_bound (R : realType) (X : metricType R)
    (alpha beta : set X -> \bar R) (V : X -> set X -> Prop)
    (W : set X) (c : R) x S :
  is_derivation_measure alpha -> is_derivation_measure beta ->
  covering_lower_sublevel V (measure_ratio_function alpha beta) c%:E W 1%R x S ->
  alpha S<=c%:E*beta S.
Proof.
move=> ha hb hS.
have hbounded := covering_lower_sublevel_bounded hS.
have haf : alpha S \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (derivation_measure_law ha) S)).
  exact: derivation_measure_bounded_finite ha S hbounded.
have hbf : beta S \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative (derivation_measure_law hb) S)).
  exact: derivation_measure_bounded_finite hb S hbounded.
have [_ [_ [_ [y [hy hlt]]]]] := hS.
have hbn : beta S!=0.
  apply/eqP=> hz.
  have hn := @measure_ratio_zero_denominator R X alpha beta S hz.
  apply: hn; by exists y.
have hbp : 0<beta S by rewrite lt_def hbn (measure_nonnegative (derivation_measure_law hb)).
exact: ltW (@finite_measure_ratio_comparison R X alpha beta S c y haf hbf hbp hy hlt).
Qed.
