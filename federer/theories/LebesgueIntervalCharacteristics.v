(** Federer (1969), 2.9.23, pp. 168–169: characteristic functions of finite
    real intervals are L1 functions, with integral their length. This is
    supporting infrastructure from 2.4.5, p. 83, and 2.5.17, p. 111,
    including empty intervals. Chapter 21 omits the counterexample. The
    local Federer erratum has no entry for pp. 168–169. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground RealOpenIntervals MeasureUP MeasureBasic
  TopologicalBorel BorelRegularMeasureUP LebesgueScalarMeasure StieltjesContinuityPoints
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureIntegralUP MeasureCharacteristicIntegral
  SummableRealFunctionUP SummableRealSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_open_interval_measurable]: supporting
    measurability of the characteristic-function sets in Federer
    2.9.23, p. 168. Open intervals are Borel sets. *)
Lemma lebesgue_open_interval_measurable (R : realType) (a b : R) :
  measure_measurable (@lebesgue_scalar_measure R) `]a,b[.
Proof.
apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  (lebesgue_scalar_borel_regular R)).
apply: open_borel_set.
have he : (`]a,b[ : set (real_line_metric R))=real_open_interval a b.
  apply/seteqP; split=> x; rewrite /real_open_interval /= in_itv /=.
  - by move=> /andP[h1 h2]; split.
  - by move=> [h1 h2]; apply/andP; split.
rewrite he; exact: real_open_interval_open.
Qed.

(** Source for [lebesgue_open_interval_length]: supporting interval
    length calculation in Federer 2.9.23, p. 168, by the
    segment law of 2.5.17, p. 111, and null endpoints. *)
Lemma lebesgue_open_interval_length (R : realType) (a b : R) :
  a<=b -> lebesgue_scalar_measure `]a,b[=(b-a)%:E.
Proof.
move=> hab; rewrite -(@measure_segment_open_interval R (@lebesgue_scalar_measure R)
  a b (lebesgue_scalar_is_measure R) (lebesgue_scalar_singleton a)
  (lebesgue_scalar_singleton b)).
exact: lebesgue_scalar_segment.
Qed.

(** Source for [lebesgue_interval_characteristic_integral]: supporting
    exact integral of chi_(0,x) in Federer 2.9.23, p. 168.
    Its value is max(x,0), including x=0 and negative x. *)
Lemma lebesgue_interval_characteristic_integral (R : realType) (x : R) :
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (@CharacteristicFunction.value R R `]0,x[))
    (Num.max x 0)%:E.
Proof.
have hi := @measure_characteristic_integral R R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) `]0,x[ _
  (@CharacteristicFunction.laws R R `]0,x[)
  (lebesgue_open_interval_measurable 0 x).
case: (leP x 0)=> hx.
- have he : (`]0,x[ : set R)=set0.
    apply/seteqP; split=> t; last by [].
    rewrite /= in_itv /= => /andP[h1 h2]; have h := lt_le_trans h2 hx.
    by have hh := lt_trans h1 h; rewrite ltxx in hh.
  have hz : lebesgue_scalar_measure `]0,x[=0%:E.
    by rewrite he (measure_empty (lebesgue_scalar_is_measure R)).
  by rewrite hz in hi.
- by rewrite lebesgue_open_interval_length ?(ltW hx) // subr0 in hi.
Qed.

(** Source for [lebesgue_interval_characteristic_summable]: supporting
    L1 membership for every value of g in Federer 2.9.23,
    p. 168. The actual characteristic integral is finite. *)
Lemma lebesgue_interval_characteristic_summable (R : realType) (x : R) :
  summable_real_functions (@lebesgue_scalar_measure R)
    (@CharacteristicFunction.value R R `]0,x[).
Proof. exists (Num.max x 0); exact: lebesgue_interval_characteristic_integral. Qed.

(** Source for [lebesgue_characteristic_curve]: direct curve g of
    Federer 2.9.23, p. 168: g(x) is the characteristic
    function of {t:0<t<x}, packed in the sealed L1 carrier. *)
Definition lebesgue_characteristic_curve (R : realType) (x : R) :
    summable_real_space (lebesgue_scalar_is_measure R) :=
  summable_real_pack (lebesgue_scalar_is_measure R)
    (lebesgue_interval_characteristic_summable x).

(** Source for [lebesgue_characteristic_curve_value]: direct value
    specification for g(x) in Federer 2.9.23, p. 168.
    Equality is pointwise, including both open endpoints. *)
Lemma lebesgue_characteristic_curve_value (R : realType) (x : R) :
  summable_real_value (lebesgue_characteristic_curve x)=
    @CharacteristicFunction.value R R `]0,x[.
Proof. exact: summable_real_packE. Qed.

(** Source for [lebesgue_characteristic_curve_nonpositive]: direct
    assertion g(x)=0 for x<=0 in Federer 2.9.23, p. 168. *)
Lemma lebesgue_characteristic_curve_nonpositive (R : realType) (x : R) :
  x<=0 -> lebesgue_characteristic_curve x=0.
Proof.
move=> hx; apply: summable_real_value_injective.
rewrite lebesgue_characteristic_curve_value linear0.
apply: funext=> t; apply: (characteristic_off_set (@CharacteristicFunction.laws R R `]0,x[)).
rewrite /= in_itv /= => /andP[h1 h2].
have hh := lt_le_trans h2 hx; by have hbad := lt_trans h1 hh; rewrite ltxx in hbad.
Qed.
