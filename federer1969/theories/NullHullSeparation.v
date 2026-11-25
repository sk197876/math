(** The final measure inequality in Federer (1969), 2.9.6, p. 155.
    Measurable supersets of two arbitrary sets with null intersection
    separate their measures. The argument uses the Caratheodory split and
    discards only a null overlap. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_overlap_measurable_covers_separate]: supporting
    final display of Federer 2.9.6, p. 155.
    Only the first containing set needs measurability;
    the target sets and second containing set may
    be arbitrary and all measure values may be infinite. *)
Lemma null_overlap_measurable_covers_separate (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (A B U W : set X) :
  is_measure phi -> A `<=` U -> B `<=` W -> measure_measurable phi U ->
  phi (U `&` W)=0 -> phi A+phi B<=phi (A `|` B).
Proof.
move=> hm hAU hBW hU hz.
have hzB : phi (B `&` U)=0.
  apply: (@measure_null_subset R X phi hm _ (U `&` W)) hz.
  move=> x [hb hu]; split=> //; exact: hBW x hb.
have hB := hU B; rewrite hzB add0e in hB.
rewrite (hU (A `|` B)) hB; apply: leeD.
- apply: (@measure_mono R X phi hm)=> x hx; split; [by left|exact: hAU x hx].
- apply: (@measure_mono R X phi hm)=> x [hx hn]; split=> //; by right.
Qed.
