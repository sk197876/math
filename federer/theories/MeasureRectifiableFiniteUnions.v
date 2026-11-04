(** Federer (1969), 3.2.47(3), p. 283: supporting
    finite assembly of the converse over compact base cores.
    Finite outer-mass rectifiability, as defined in 3.2.14(4),
    p. 252, survives finite unions of arbitrary original sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import RectifiableSetUP CountablyMeasureRectifiableOperations
  MeasureUP MeasureBasic MeasureFiniteUnionBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_rectifiable_finite_union]: finite
    patch reduction in 3.2.47(3), p. 283, retaining
    both the countable almost-cover and finite-mass requirements
    of 3.2.14(4), p. 252, without measurability assumptions. *)
Theorem measure_rectifiable_finite_union (R:realType) (X:metricType R) (J:finType)
    (phi:set X->\bar R) m (F:J->set X):
  is_measure phi ->(forall i,is_measure_m_rectifiable phi m (F i)) ->
  is_measure_m_rectifiable phi m (\bigcup_i F i).
Proof.
move=>hPhi hF; split.
- apply:(@countably_measure_rectifiable_countable_union R X J phi m setT F hPhi
    (countableP setT)).
  by move=>i _; exact:(hF i).1.
- have hValue i:phi (F i)=(fine (phi (F i)))%:E.
    have hFinite:phi (F i) \is a fin_num.
      rewrite ge0_fin_numE; first exact:(hF i).2.
      exact (@measure_nonnegative R X phi hPhi (F i)).
    by rewrite fineK.
  have hSum: \sum_i phi (F i)=(\sum_i fine (phi (F i)))%:E.
    rewrite -sumEFin; apply:eq_bigr=>i _; exact:hValue i.
  have hFinite:(\sum_i phi (F i))< +oo by rewrite hSum ltry.
  exact:(le_lt_trans (@measure_finite_union_bound R X J phi F hPhi) hFinite).
Qed.
