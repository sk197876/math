(** Federer (1969), 3.2.22, pp. 258–260: the
    degree-zero target remainder is empty, by the H^0
    counting convention of 2.10.2, p. 171. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import HausdorffMeasure HausdorffCountingMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_zero_null_set_empty]: supporting
    degree-zero boundary of Federer 3.2.22, pp. 258–260.
    H^0 is counting measure by 2.10.2, p. 171,
    so every nonempty subset has mass at least one. *)
Lemma hausdorff_zero_null_set_empty (R:realType) (X:metricType R) (A:set X):
  @hausdorff_measure R X 0 A=0 ->A=set0.
Proof.
move=>hA; apply/seteqP; split=>[x hx|x []].
have hSub:[set x] `<=` A by move=>y ->.
have hZero:=measure_null_subset (@hausdorff_measure_is_measure R X 0) hSub hA.
rewrite hausdorff_zero_singleton in hZero.
by move:hZero=>/eqP; rewrite eqe oner_eq0.
Qed.
