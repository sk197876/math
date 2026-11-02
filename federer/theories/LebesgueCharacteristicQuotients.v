(** Federer (1969), 2.9.23, pp. 168–169: the difference quotients of
    chi_(0,x) have integral one for positive increments, and are supported
    in intervals shrinking to x. This is the calculation behind the asserted
    failure of weak convergence. The local Federer erratum has no entry
    here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground MeasureUP TopologicalBorel
  BorelRegularMeasureUP IntervalBumpFunctions LebesgueScalarMeasure
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealSpace SummableRealIntegralMap
  SummableCharacteristicFunctional LebesgueIntervalCharacteristics
  LebesgueCharacteristicCurveLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_closed_test_interval_measurable]: supporting
    measurable characteristic tests for Federer 2.9.23, p. 169.
    Closed intervals are Borel sets, including singleton intervals. *)
Lemma lebesgue_closed_test_interval_measurable (R : realType) (a b : R) :
  measure_measurable (@lebesgue_scalar_measure R) `[a,b].
Proof.
apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  (lebesgue_scalar_borel_regular R)).
apply: closed_borel_set; exact: segment_closed_real.
Qed.

(** Source for [lebesgue_characteristic_quotient]: direct difference
    quotient (g(x+h)-g(x))/h in Federer 2.9.23, p. 169.
    Only its laws at nonzero h are used for limits. *)
Definition lebesgue_characteristic_quotient (R : realType) (x h : R) :=
  h^-1 *: (lebesgue_characteristic_curve (x+h)-lebesgue_characteristic_curve x).

(** Source for [lebesgue_characteristic_quotient_integral]: supporting
    unit integral of the positive-increment quotients in Federer
    2.9.23, p. 169. The endpoint x is strictly positive. *)
Lemma lebesgue_characteristic_quotient_integral (R : realType) (x h : R) :
  0<x -> 0<h -> summable_real_integral_map (lebesgue_characteristic_quotient x h) = 1.
Proof.
move=> hx hh; rewrite /lebesgue_characteristic_quotient linearZ linearB /=
  !lebesgue_characteristic_curve_integral.
change (h^-1 * (Num.max (x+h) 0-Num.max x 0) = 1).
have hxh : 0<=x+h by lra.
rewrite (max_l hxh) (max_l (ltW hx)).
have he : x+h-x=h by lra.
by rewrite he mulVf ?gt_eqF.
Qed.

(** Source for [lebesgue_characteristic_quotient_support]: supporting
    concentration of the quotient in [x,x+h] for Federer
    2.9.23, p. 169. Keeping the closed hull avoids changing
    the exact open-endpoint convention in the original g. *)
Lemma lebesgue_characteristic_quotient_support (R : realType) (x h : R) :
  0<x -> 0<h -> forall t : R, ~ `[x,x+h] t ->
    summable_real_value (lebesgue_characteristic_quotient x h) t=0.
Proof.
move=> hx hh t ht; rewrite /lebesgue_characteristic_quotient linearZ linearB
  /= !fctE !lebesgue_characteristic_curve_value.
change (h^-1 * (@CharacteristicFunction.value R R `]0,x+h[ t -
  @CharacteristicFunction.value R R `]0,x[ t)=0).
have hA := @CharacteristicFunction.laws R R `]0,x+h[.
have hB := @CharacteristicFunction.laws R R `]0,x[.
case: (ltP t x)=> htx.
- case: (ltP 0 t)=> ht0.
  + have ha : `]0,x+h[ t by rewrite /= in_itv /= ht0; lra.
    have hb : `]0,x[ t by rewrite /= in_itv /= ht0 htx.
    by rewrite (characteristic_on_set hA ha) (characteristic_on_set hB hb) subrr mulr0.
  + have ha : ~ `]0,x+h[ t.
      rewrite /= in_itv /= => /andP[h0 _]; by have hbad := lt_le_trans h0 ht0; rewrite ltxx in hbad.
    have hb : ~ `]0,x[ t.
      rewrite /= in_itv /= => /andP[h0 _]; by have hbad := lt_le_trans h0 ht0; rewrite ltxx in hbad.
    by rewrite (characteristic_off_set hA ha) (characteristic_off_set hB hb) subrr mulr0.
- have hxt : x+h<t.
    apply: contrapT=> hn; have hle : t<=x+h by rewrite leNgt; exact/negP.
    apply: ht; by rewrite /= in_itv /= htx hle.
  have ha : ~ `]0,x+h[ t.
    rewrite /= in_itv /= => /andP[_ h1]; by have hbad := lt_trans h1 hxt; rewrite ltxx in hbad.
  have hb : ~ `]0,x[ t.
    rewrite /= in_itv /= => /andP[_ h1]; by have hbad := lt_le_trans h1 htx; rewrite ltxx in hbad.
  by rewrite (characteristic_off_set hA ha) (characteristic_off_set hB hb) subrr mulr0.
Qed.

(** Source for [lebesgue_characteristic_quotient_test]: supporting
    value one under the characteristic test of [x,x+r] for every
    positive h<=r, in the weak-limit assertion of Federer
    2.9.23, p. 169. The test is fixed before h tends to zero. *)
Lemma lebesgue_characteristic_quotient_test (R : realType) (x r h : R) :
  0<x -> 0<h -> h<=r ->
  summable_characteristic_functional (lebesgue_closed_test_interval_measurable x (x+r))
    (lebesgue_characteristic_quotient x h) = 1.
Proof.
move=> hx hh hhr.
pose A : set R := `[x,x+r].
pose q := lebesgue_characteristic_quotient x h.
have hs := @CharacteristicFunction.laws R R A.
have he : (fun t => summable_real_value q t * @CharacteristicFunction.value R R A t)=
    summable_real_value q.
  apply: funext=> t; case: (pselect (A t))=> ht.
  - by rewrite (characteristic_on_set hs ht) mulr1.
  - have hn : ~ `[x,x+h] t.
      move=> hI; apply: ht; move: hI; rewrite /A /= !in_itv /= => /andP[h1 h2].
      apply/andP; split=> //; lra.
    have hz := lebesgue_characteristic_quotient_support hx hh hn.
    by rewrite /q hz mul0r.
have hi := (summable_characteristic_functional_specification
  (lebesgue_closed_test_interval_measurable x (x+r)) q).1.
rewrite he in hi.
have heq := EFin_inj (measure_integral_unique hi (summable_real_integral_map_specification q)).
by rewrite heq /q lebesgue_characteristic_quotient_integral.
Qed.
