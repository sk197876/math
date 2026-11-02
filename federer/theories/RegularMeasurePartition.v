(** Federer (1969), 2.1.5(3), pp. 56-57: finite additive partitions of a
    measurable set under regularity. it does not give this assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure
  MeasureFiniteAdditivity RegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [regular_measure_additive_partition_left]: Federer
    2.1.5(3), proof p. 57; choose a measurable C between A and
    A union B, use inclusion-exclusion to prove C intersection B
    null, and remove the null excess C minus A. *)
Lemma regular_measure_additive_partition_left (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (hr : is_regular_measure mu)
    (A B : set I) :
  measure_measurable mu (A `|` B) ->
  mu A + mu B = mu (A `|` B) -> mu (A `|` B) < +oo ->
  measure_measurable mu A.
Proof.
move=> hU he hf; have [D [hAD [hD hval]]] := hr A.
pose C := D `&` (A `|` B).
have hC : measure_measurable mu C := @measure_measurable_intersection R I mu hm D (A `|` B) hD hU.
have hAC : A `<=` C.
  move=> x hx; split; first exact: hAD; by left.
have hCD : C `<=` D by move=> x [hx _].
have hCU : C `|` B = A `|` B.
  apply/seteqP; split.
  - by move=> x [[_ hx]|hx]; last right.
  - move=> x [hx|hx]; [left; exact: hAC | by right].
have hCA : mu C = mu A.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - rewrite hval; exact: (@measure_mono R I mu hm _ _ hCD).
  - exact: (@measure_mono R I mu hm _ _ hAC).
have hzero : mu (C `&` B) = 0.
  have h := @measure_inclusion_exclusion R I mu C B hC.
  rewrite hCA he hCU in h.
  have hq : mu (A `|` B) \is a fin_num.
    by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R I mu hm).
  have hz := congr1 (fun t => t - mu (A `|` B)) h.
  by rewrite subee // addeK // in hz.
have hnull : mu (C `\` A) = 0.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT -hzero.
  apply: (@measure_mono R I mu hm _ _)=> x [hc hn]; split=> //.
  have [_ [ha|hb]] := hc; [by exfalso; exact: hn | exact hb].
have hN := @measure_null_measurable R I mu hm (C `\` A) hnull.
have hEq : C `\` (C `\` A) = A.
  apply/seteqP; split.
  - move=> x [hc hn]; case: (pselect (A x))=> ha //.
    exfalso; apply: hn; by split.
  - move=> x ha; split; first exact: hAC.
    by move=> [_ hn]; exact: hn.
have h := @measure_measurable_difference R I mu hm C (C `\` A) hC hN.
by rewrite hEq in h.
Qed.

(** Source for [regular_measure_additive_partition]: Federer
    2.1.5(3), p. 56; both parts are measurable if their union is
    measurable and their measures add to its finite measure. *)
Theorem regular_measure_additive_partition (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (hr : is_regular_measure mu)
    (A B : set I) :
  measure_measurable mu (A `|` B) ->
  mu A + mu B = mu (A `|` B) -> mu (A `|` B) < +oo ->
  measure_measurable mu A /\ measure_measurable mu B.
Proof.
move=> hU he hf; split.
- exact: (@regular_measure_additive_partition_left R I mu hm hr A B hU he hf).
- apply: (@regular_measure_additive_partition_left R I mu hm hr B A);
    by rewrite ?(setUC B A) ?(addeC (mu B) (mu A)).
Qed.
