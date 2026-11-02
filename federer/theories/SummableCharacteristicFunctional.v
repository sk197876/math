(** Federer (1969), 2.9.23, p. 169: integration against bounded measurable
    tests detects failure of weak convergence. Characteristic tests suffice
    for the contradiction below. Their bound is the endpoint Holder
    inequality of 2.4.14, p. 88, and their small-set estimate is 2.4.11, pp.
    85–86. The local Federer erratum has no entry for this example. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialZeroExtension PartialAbsolutePartsGraph MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableNormedCharacteristic CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence
  MeasureIntegralAbsolute MeasureIntegralAbsoluteContinuity MeasureSubsetIntegral
  SummableRealFunctionUP SummableRealArithmetic SummableRealSpace SummableRealSeminorm
  TotalScalarLpUP TotalScalarPairing TotalScalarPairingValue SeminormWeakLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Functional.
Variable R : realType.
Variable X : choiceType.
Variable mu : set X -> \bar R.
Variable hm : is_measure mu.
Variable A : set X.
Variable hA : measure_measurable mu A.

(** Source for [summable_characteristic_functional]: supporting
    linear test f -> integral_A f for the weak-limit assertion
    of Federer 2.9.23, p. 169. The integral value comes
    from the existing sealed pairing, and A need not be finite. *)
Definition summable_characteristic_functional (f : summable_real_space hm) : R^o :=
  let _ := hA in total_scalar_pairing mu (summable_real_value f)
    (@CharacteristicFunction.value R X A).

(** Source for [summable_characteristic_functional_specification]:
    supporting actual test integral in Federer 2.9.23, p. 169.
    Summability and the norm bound follow from the bounded factor
    estimate, including infinite-measure test sets. *)
Lemma summable_characteristic_functional_specification f :
  is_measure_integral mu (real_total_integrand
    (fun x => summable_real_value f x * @CharacteristicFunction.value R X A x))
    (summable_characteristic_functional f)%:E /\
  `|summable_characteristic_functional f|<=summable_real_seminorm f.
Proof.
have hs := @CharacteristicFunction.laws R X A.
have hsm := (@measurable_normed_characteristic R X mu hm A _ hs hA).1.
have hb : measure_almost_everywhere mu
    [set x | `|@CharacteristicFunction.value R X A x|<= 1].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  change (is_true (`|@CharacteristicFunction.value R X A x|<= 1)).
  case: (pselect (A x))=> hx.
  - by rewrite (characteristic_on_set hs hx) normr1.
  - by rewrite (characteristic_off_set hs hx) normr0 ler01.
have [c [hi hc]] := @total_scalar_pairing_bounded_factor R X mu hm
  (summable_real_value f) (@CharacteristicFunction.value R X A) 1
  (summable_real_value_lone f) hsm ler01 hb.
have he := total_scalar_pairing_value_of_integral hi.
rewrite /summable_characteristic_functional he; split=> //.
by rewrite mul1r in hc.
Qed.

(** Source for [summable_characteristic_functional_linear]: supporting
    linearity of the bounded test in Federer 2.9.23, p. 169,
    by the finite integral laws in 2.4.4(3)–(4), p. 82. *)
Lemma summable_characteristic_functional_linear : linear summable_characteristic_functional.
Proof.
have hs (f : summable_real_space hm) : summable_real_functions mu
    (fun x => summable_real_value f x * @CharacteristicFunction.value R X A x).
  exists (summable_characteristic_functional f).
  exact: (summable_characteristic_functional_specification f).1.
move=> c f g.
have he : summable_real_value (c *: f+g)=
    (fun x => c*summable_real_value f x+summable_real_value g x).
  by rewrite linearP !fctE.
have hcf : summable_real_functions mu
    (fun x => c*summable_real_value f x * @CharacteristicFunction.value R X A x).
  have hi := @real_total_integral_scale R X mu hm _ _ c
    (summable_characteristic_functional_specification f).1.
  exists (c*summable_characteristic_functional f).
  have hh : (fun x => c*(summable_real_value f x * @CharacteristicFunction.value R X A x))=
      (fun x => c*summable_real_value f x * @CharacteristicFunction.value R X A x).
    by apply: funext=> x; rewrite mulrA.
  by rewrite -hh.
rewrite /summable_characteristic_functional he
  (@total_scalar_pairing_add_left R X mu hm _ _ _ hcf (hs g)).
by rewrite (@total_scalar_pairing_scale_left R X mu hm _ _ c (hs f)).
Qed.
HB.instance Definition _ := GRing.isLinear.Build R (summable_real_space hm) R^o
  *:%R summable_characteristic_functional summable_characteristic_functional_linear.

(** Source for [summable_characteristic_functional_bounded]: supporting
    continuous dual membership for the test used in Federer 2.9.23,
    p. 169. Its seminorm bound is one, even when A is null. *)
Lemma summable_characteristic_functional_bounded :
  seminorm_bounded_real_functional (@summable_real_seminorm R X mu hm)
    (summable_characteristic_functional : {linear summable_real_space hm -> R^o}).
Proof.
exists 1; split; first exact: ler01.
by move=> f; rewrite mul1r; exact: (summable_characteristic_functional_specification f).2.
Qed.
End Functional.
