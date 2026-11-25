(** Federer (1969), 2.5.3, p. 94, fourth further condition, with the
    deduction indicated on p. 95. Finite test sets are covered by closed
    unit levels; infinite test sets satisfy the splitting identity from the
    measure's covering inequality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP DaniellCoverUP DaniellFiniteUnitLevelCover
  RepresentedLatticeClosedLevels RealIntegralFunctionalUP MeasureUP MeasureBasic MeasureSplit
  MeasureFiniteClosure MeasureCountableClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_measurable_iff_unit_level_intersections]: direct
    fourth further condition of Federer 2.5.3, p. 94 The test ranges over
    all positive lattice functions and all subsets B. *)
Theorem daniell_measurable_iff_unit_level_intersections (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu L A) (hc : is_daniell_cover_envelope L A mu) (B : set X) :
  measure_measurable mu B <-> forall f, positive_function_lattice L f ->
    measure_measurable mu (B `&` [set x | (1 <= f x)%R]).
Proof.
split.
- move=> hB f hf; apply: (@measure_measurable_intersection R X mu hm B _ hB).
  exact: (@represented_lattice_closed_upper_level_measurable R X L A mu hm hA f 1%R hf.1).
- move=> htest T; case: (ltP (mu T) +oo)=> hfin.
  + have [f [hf hcover]] := @daniell_finite_unit_level_cover R X L A hL mu hm hc T hfin.
    pose C := \bigcup_(n in setT) (B `&` [set x | (1 <= f n x)%R]).
    have hC : measure_measurable mu C.
      apply: (@measure_measurable_sequence_union R X mu hm (fun n => B `&` [set x | (1 <= f n x)%R]))=> n.
      exact: htest (f n) (hf n).
    have hTC : T `&` C=T `&` B.
      apply/seteqP; split=> x [hx hy].
      * have [n _ [hB hn]] := hy; by split.
      * split=> //; have [n _ hn] := hcover x hx; exists n=> //; by split.
    have hTD : T `\` C=T `\` B.
      apply/seteqP; split=> x [hx hy]; split=> //.
      * move=> hB; apply: hy; have [n _ hn] := hcover x hx; exists n=> //; by split.
      * move=> [n _ [hB hn]]; exact: hy hB.
    by rewrite -(hTC) -(hTD); exact: hC.
  + apply/eqP; rewrite eq_le (measure_split_upper hm) /=.
    exact: le_trans (leey _) hfin.
Qed.
