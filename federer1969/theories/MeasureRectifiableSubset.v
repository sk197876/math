(** Federer (1969), 3.2.22(2), p. 258: the
    degree-zero target case uses hereditary source rectifiability.
    This is a direct consequence of 3.2.14(3)–(4),
    pp. 251–252, and monotonicity of the measure. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import RectifiableSetUP CountablyMeasureRectifiableOperations MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_rectifiable_subset]: supporting
    mu=0 fibre boundary in Federer 3.2.22(2),
    p. 258. Every subset of a (phi,m)
    rectifiable set has the same countable cover up
    to a null set and has no larger finite mass.
    Neither source nor subset measurability is needed. *)
Lemma measure_rectifiable_subset (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (E F:set X):
  F `<=` E ->is_measure_m_rectifiable phi m E ->is_measure_m_rectifiable phi m F.
Proof.
move=>hFE [hE hFinite]; split.
- exact:(countably_measure_rectifiable_subset hFE hE).
- exact:(le_lt_trans (measure_mono hE.1 hFE) hFinite).
Qed.
