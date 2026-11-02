(** Federer (1969), 2.9.18(1), p. 163: existence of the positive-length
    nowhere dense compact target assumed in the example. The book does not
    construct this target there. We remove a dense open set of small length
    from [0,1], using only the earlier Borel regularity and
    countable-null-set laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology num_normedtype normed_module lra.
From Federer Require Import RealMetricBackground RealLineSeparability NowhereDenseUP ScalarLebesgueBallContext
  LebesgueScalarMeasure IntervalBumpFunctions MeasureUP MeasureBasic MeasureSplit DerivationOpenSupersets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_length_nowhere_dense_compact_exists]:
    existence support for the target T in Federer 2.9.18(1),
    p. 163. A countable dense real set is null;
    surround it by an open set of length at most 1/4
    and remove that open set from the unit interval. The
    remainder is compact, nowhere dense, and has positive length.
    This supplies a witness instead of assuming such a target. *)
Theorem positive_length_nowhere_dense_compact_exists (R : realType) :
  exists T : set (real_line_metric R),
    compact T /\ is_nowhere_dense T /\ (0<lebesgue_scalar_measure T)%E.
Proof.
have hm := lebesgue_scalar_is_measure R.
have [D [hDc hDd]] := real_line_countable_dense R.
have hDzero := scalar_lebesgue_countable_null hDc.
have hquarter : (0<1/4 :> R) by rewrite divr_gt0 // ltr0n.
have [W [hW [hDW hmass]]] := @derivation_measure_open_superset R
  [the metricType R of real_line_metric R] (@lebesgue_scalar_measure R) D (1/4)
  (scalar_lebesgue_derivation_class R) hquarter.
rewrite hDzero add0e in hmass.
pose T : set (real_line_metric R) := `[0,1] `\` W.
have hTclosed : closed T.
  rewrite /T setDE; apply: closedI; first exact: segment_closed_real.
  exact: open_closedC hW.
have hTcompact : compact T.
  rewrite /T setDE.
  exact (@compact_closedI [the topologicalType of real_line_metric R]
    `[0,1] (~` W) (@segment_compact R 0 1) (open_closedC hW)).
have hnowhere : is_nowhere_dense T.
  rewrite /is_nowhere_dense -((closure_id T).1 hTclosed).
  move=> U hUn hU.
  have [x [hxU hxD]] := hDd U hUn hU.
  exists x; split=> // -[_ hnW]; exact: hnW (hDW x hxD).
have hnonzero : lebesgue_scalar_measure T!=0%E.
  apply/negP=> /eqP hz.
  have hcover : `[0,1] `<=` W `|` T.
    move=> x hx; case: (pselect (W x))=> hw; first by left.
    right; by split.
  have hb := @measure_binary_cover R R (@lebesgue_scalar_measure R) hm `[0,1] W T hcover.
  rewrite (@lebesgue_scalar_segment R 0 1 (ler01)) subr0 hz adde0 in hb.
  have hcontr := le_trans hb hmass.
  have hbad : (1<=1/4 :> R) by move: hcontr; rewrite lee_fin.
  have hsmall : (1/4<1 :> R) by rewrite ltr_pdivrMr ?ltr0n // mul1r ltr1n.
  by have := lt_le_trans hsmall hbad; rewrite ltxx.
exists T; split=> //; split=> //.
by rewrite lt_neqAle eq_sym hnonzero (measure_nonnegative hm).
Qed.
