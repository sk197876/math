(** Federer (1969), 2.2.12, p. 69: choose the next coordinate bound by
    continuity from below of the regularised measure, even though the
    projected sets need not be measurable. Source context: SequenceBoxes.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace SequenceFiniteBounds MeasureUP MeasureBasic
  RegularMeasureUP RegularMeasureContinuity ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_projection_coordinate_approximation]: direct
    single-step choice in Federer 2.2.12, p. 69. Increasing
    a coordinate bound exhausts the projection of the preceding
    witness. The finite-measure loss inequality is written as an
    equivalent additive bound, avoiding a partial subtraction. *)
Lemma regular_projection_coordinate_approximation (R : realType) (X : topologicalType)
    (gamma : set X -> \bar R) (hm : is_measure gamma) (hr : is_regular_measure gamma)
    (W : set (X * positive_sequence_space R)) k (epsilon : R) :
  gamma setT < +oo -> (0 < epsilon)%R -> exists m,
  gamma (fst @` W) < gamma (fst @` (W `&`
    [set p | sequence_coordinate_bound k m p.2])) + epsilon%:E.
Proof.
move=> htotal he.
pose A m := fst @` (W `&` [set p | sequence_coordinate_bound k m p.2]).
have hmono n m : (n <= m)%N -> A n `<=` A m.
  move=> hnm x [p [hp hb] <-]; exists p=> //; split=> //.
  exact: leq_trans hb hnm.
have hcover : (\bigcup_m A m) = fst @` W.
  apply/seteqP; split.
  - move=> x [m _ [p [hp _] <-]]; by exists p.
  - move=> x [p hp <-]; exists (positive_sequence_coordinates p.2 k); first exact Logic.I.
    exists p=> //; split=> //; exact: leqnn.
have hlim := @regular_measure_continuity_below R X gamma hm hr A hmono.
rewrite hcover in hlim.
have hfin : gamma (fst @` W) \is a fin_num.
  rewrite ge0_fin_numE; last exact: (@measure_nonnegative R X gamma hm).
  apply: le_lt_trans (_ : gamma (fst @` W) <= gamma setT) htotal.
  apply: (@measure_mono R X gamma hm)=> x hx; exact Logic.I.
have hlt : gamma (fst @` W) - epsilon%:E < gamma (fst @` W).
  rewrite lte_subel_addr // -{1}[gamma (fst @` W)]adde0 lteD2lE // lte_fin; exact he.
have [m hmnear] := hlim.2.1 _ hlt.
exists m; have hh := hmnear m (leqnn m).
by rewrite lte_subel_addr in hh.
Qed.
