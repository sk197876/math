(** Federer (1969), 2.9.22, p. 168: if L^1(Z)=0, then s'(x)=0 almost
    everywhere on s^{-1}(Z), for nondecreasing s. The proof uses the actual
    derivative variation measure, its segment bound and Borel null hulls, so
    no false assertion about ordinary inverse images of null sets is
    assumed. Chapter 21 has no matching reflexive-curve item. The
    diameter-cover passage to sets is documented in
    MonotoneDerivativeImageBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength CurveVariationUP
  StieltjesMonotone StieltjesImageMeasures DerivativeVariationMeasure
  DerivativeVariationNullity MonotoneDerivativeImageBound RealCurveDerivativeUP
  MeasureUP MeasureBasic MeasureAlmostUP LebesgueScalarMeasure
  BorelRegularMeasureUP TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [monotone_derivative_variation_image_bound]: direct
    weighted inverse-image estimate supporting Federer 2.9.22,
    p. 168. For monotone s, its absolute derivative equals s'
    wherever it exists. Its derivative variation measure has image
    at most L^1 on every subset, with no measurability restriction. *)
Theorem monotone_derivative_variation_image_bound (R : realType)
    (s : R -> R) (psip psim : set R -> \bar R) :
  (forall a b, a<=b -> s a<=s b) -> is_induced_measure_pair s psip psim ->
  forall A, (real_derivative_variation_measure psip psim (s @^-1` A)
    <=lebesgue_scalar_measure A)%E.
Proof.
move=> hs hp.
have hfin := @monotone_locally_finite_variation R s hs.
have [hn [hrep [hz hbound]]] := @real_derivative_variation_measure_laws R s psip psim hfin hp.
have hmeas a b : measure_measurable (real_derivative_variation_measure psip psim) `[a,b].
  have hAm : measure_measurable (@lebesgue_scalar_measure R) `[a,b].
    apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
      (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R)).
    exact: closed_borel_set (@segment_closed_real R a b).
  exact (hrep `[a,b] hAm).1.
have hb a b : a<=b -> (real_derivative_variation_measure psip psim `[a,b]<=(s b-s a)%:E)%E.
  move=> hab; have h := hbound a b hab.
  by rewrite (@monotone_curve_variation_eq R s hs a b hab) in h.
exact (@monotone_atomless_measure_image_bound R s _ hn hs hz hmeas hb).
Qed.

(** Source for [monotone_null_preimage_zero_derivative]: direct
    conclusion following the weighted inverse-image inequality in
    Federer 2.9.22, p. 168. The original null set Z may be
    arbitrary. The derivative is the actual two-sided derivative,
    with no value assigned at nondifferentiability points. *)
Theorem monotone_null_preimage_zero_derivative (R : realType)
    (s : R -> R) (Z : set (real_line_metric R)) :
  (forall a b, a<=b -> s a<=s b) -> lebesgue_scalar_measure Z=0%E ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | Z (s x) -> has_real_curve_derivative s x 0].
Proof.
move=> hs hZ.
have hfin := @monotone_locally_finite_variation R s hs.
have [psip [psim hp]] := @induced_measure_pair_exists R s hfin.
have hbound := @monotone_derivative_variation_image_bound R s psip psim hs hp Z.
have [hn _] := @real_derivative_variation_measure_laws R s psip psim hfin hp.
have hzero : real_derivative_variation_measure psip psim (s @^-1` Z)=0%E.
  apply: le_anti; by rewrite hZ in hbound; rewrite hbound (measure_nonnegative hn).
exact (@real_derivative_zero_on_variation_null R s psip psim (s @^-1` Z) hfin hp hzero).
Qed.
