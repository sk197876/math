(** Federer (1969), 3.2.14, p. 252: purely
    unrectifiable sets contain no positive-mass
    rectifiable subset. State the equivalent null-set
    formulation and its hereditary consequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic RectifiableSetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pure_unrectifiable_iff_rectifiable_subsets_null]:
    equivalent null-mass formulation of the definition
    in Federer 3.2.14, p. 252. The measure law,
    rather than an extra sign assumption, gives nonnegativity. *)
Theorem pure_unrectifiable_iff_rectifiable_subsets_null (R : realType)
    (X : metricType R) (phi : set X -> \bar R) m (E : set X) :
  is_purely_measure_m_unrectifiable phi m E <->
  is_measure phi /\ forall F, F `<=` E -> is_m_rectifiable m F -> phi F=0.
Proof.
split.
- move=> [hm hn]; split=> // F hFE hF.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
  apply/negP=> hpos; apply: hn; exists F; by split=> //; split.
- move=> [hm hnull]; split; first exact hm.
  move=> [F [hFE [hF hpos]]].
  by rewrite (hnull F hFE hF) ltxx in hpos.
Qed.

(** Source for [pure_unrectifiable_subset]: restricting
    a purely unrectifiable set in the definition of
    Federer 3.2.14, p. 252. No measurability of
    the subset is needed. *)
Lemma pure_unrectifiable_subset (R : realType)
    (X : metricType R) (phi : set X -> \bar R) m (E F : set X) :
  F `<=` E -> is_purely_measure_m_unrectifiable phi m E ->
  is_purely_measure_m_unrectifiable phi m F.
Proof.
move=> hFE [hm hn]; split; first exact hm.
move=> [G [hGF [hG hpos]]].
apply: hn; exists G; split; last by split.
move=> x hx; exact: hFE x (hGF x hx).
Qed.
