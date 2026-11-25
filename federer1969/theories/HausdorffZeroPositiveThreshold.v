(** Federer (1969), 3.2.32, pp. 269–270: supporting
    positive-atom boundaries, using the counting convention of
    2.10.2, p. 171. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import HausdorffMeasure HausdorffCountingMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_zero_positive_iff_unit_threshold]: supporting
    the zero complementary degree in Federer 3.2.32,
    p. 269. Positive H^0 mass is equivalent to mass at
    least one, because every nonempty set contains an actual
    unit atom. This is a consequence of 2.10.2, p. 171. *)
Lemma hausdorff_zero_positive_iff_unit_threshold (R:realType) (X:metricType R) (A:set X):
  (0<@hausdorff_measure R X 0 A)=(1<=@hausdorff_measure R X 0 A).
Proof.
apply/idP/idP.
- move=>hPos.
  have [hIn|hIn]:=pselect (exists x,A x).
  + have [x hx]:=hIn.
    rewrite -(@hausdorff_zero_singleton R X x).
    apply:(measure_mono (@hausdorff_measure_is_measure R X 0))=>y ->; exact hx.
  + have hEmpty:A=set0 by apply/seteqP; split=>[x hx|x []]; exfalso; apply:hIn; by exists x.
    by rewrite hEmpty (measure_empty (@hausdorff_measure_is_measure R X 0)) ltxx in hPos.
- move=>hOne; apply:lt_le_trans _ hOne; by rewrite lte_fin ltr01.
Qed.
