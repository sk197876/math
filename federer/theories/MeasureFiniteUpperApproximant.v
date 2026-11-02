(** Federer (1969), 2.4.3(4), p. 82: a finite upper bound on the upper
    integral supplies an upper step function with assigned sum below
    positive infinity. Its real values then show f(x)<infinity almost
    everywhere. Source context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureStepFunctionUP MeasureIntegralUP MeasureIntegralBounds PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_upper_value_below]: supporting strict
    infimum approximation in Federer 2.4.3(4),(6), p. 82,
    using only the defining greatest-lower-bound law. *)
Lemma measure_upper_value_below (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R)) b :
  measure_upper_integral mu f < b -> exists a, measure_upper_step_values mu f a /\ a < b.
Proof.
move=> hb; case: (pselect (exists a, measure_upper_step_values mu f a /\ a < b))=> [//|hn].
exfalso; have hle : b <= measure_upper_integral mu f.
  apply: (measure_upper_integral_specification mu f).2=> a ha.
  rewrite leNgt; apply/negP=> hab; apply: hn; exists a; by split.
by move: hb; rewrite ltNge hle.
Qed.

(** Source for [measure_finite_upper_approximant]: supporting
    upper step function for Federer 2.4.3(4), p. 82.
    Its assigned value may be negative infinity; only positive
    infinity is excluded at this stage. *)
Lemma measure_finite_upper_approximant (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f : partial_function X (extended_real_line R)) :
  measure_upper_integral mu f < +oo -> exists u a,
    is_measure_upper_function mu f u /\ is_measure_step_integral mu u a /\ a < +oo.
Proof.
move=> hf; have [a [[u [hu ha]] hb]] := @measure_upper_value_below R X mu f +oo hf.
exists u,a; by split=> //; split.
Qed.

(** Source for [finite_upper_integral_below_infinity_almost]:
    the pointwise conclusion of Federer 2.4.3(4), p. 82.
    This is the second part of the printed conclusion; the positive-
    part upper-integral estimate is proved separately. *)
Theorem finite_upper_integral_below_infinity_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) :
  measure_upper_integral mu f < +oo ->
  measure_almost_everywhere mu (partial_extended_below_infinity_locus f).
Proof.
move=> hf; have [u [a [[hu hlu] [ha hfin]]]] := @measure_finite_upper_approximant R X mu f hf.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlu).
move=> x [y [z [hy [hz hzy]]]]; exists z; split=> //.
exact: le_lt_trans hzy (ltry y).
Qed.
