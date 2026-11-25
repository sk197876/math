(** Federer (1969), 4.1.23, p. 379: the
    step-field reduction uses constant multivectors on
    finite measurable cells inside one compact carrier.
    The actual Omega representative retains every point
    value and its exact mass cost, with no
    positivity or completeness assumption on the coefficient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  PartialNormPower RealPower MeasureUP MeasureBasic MeasureIntegralUP MeasureIntegralUniqueness
  MeasureIntegralGraphEquivalence SummableRealFunctionUP SummableRealArithmetic
  CharacteristicFunctionUP CharacteristicFunctionSealed CharacteristicVectorPiece
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureCharacteristicIntegral
  MeasureLpNorm MeasureLoneNormIntegralGeneral CompactSummableFieldSealed
  CompactSummableFieldLaws CompactSummableFieldRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactCharacteristicField.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation W := (@CompactSummableField.space R X V N hN mu hm).
Local Notation value := (@compact_summable_field_value R X V N hN mu hm).
Local Notation size := (@compact_summable_field_size R X V N hN mu hm).
Variable A : set X.
Hypothesis hA : measure_measurable mu A.
Hypothesis hFinite : (mu A< +oo)%E.
Local Notation chi := (@CharacteristicFunction.value R X A).
Local Notation hChi := (@CharacteristicFunction.laws R X A).

(** Source for [compact_characteristic_summable_field_exists]:
    every cell in the step-field reduction
    of Federer 4.1.23, p. 379,
    has an actual compactly supported summable
    representative chi_A z. Its cost is
    exactly mass(z) times measure(A), including
    zero coefficients, null cells and empty carriers. *)
Theorem compact_characteristic_summable_field_exists
    (K : set X) (hK : compact K) (hAK : A `<=` K) (z : V) :
  exists f : W,
    (forall x, value f x=chi x*:z) /\
    (size f)%:E=((N z)%:E*mu A)%E /\
    forall x, ~K x -> value f x=0.
Proof.
pose g := fun x : X => (chi x*:z : real_norm_metric_space hN).
have hMeas := @measurable_normed_characteristic_piece R X V N hN mu hm
  A chi (fun _ : X => (z:real_norm_metric_space hN)) hChi hA
  (@measurable_normed_total_constant R X V N hN mu hm z).
have hNumber : mu A \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm A)); exact: hFinite.
pose a := fine (mu A).
have hMu : mu A=a%:E by rewrite /a fineK.
have hChiIntegral := @measure_characteristic_integral R X mu hm A chi hChi hA.
rewrite hMu in hChiIntegral.
have hScale := @real_total_integral_scale R X mu hm chi a (N z) hChiIntegral.
have hNormFunction : (fun x : X => N (g x))=(fun x => N z*chi x).
  apply: funext=> x; rewrite /g; case: (pselect (A x))=> hx.
  - by rewrite (characteristic_on_set hChi hx) scale1r mulr1.
  - by rewrite (characteristic_off_set hChi hx) scale0r
      (real_seminorm_zero hN.1) mulr0.
have hPowerIntegral := @measurable_lone_norm_integral R X V N hN mu hm
  (partial_function_total g) hMeas.1.
have hNormIntegral : is_measure_integral mu
    (real_total_integrand (fun x => N (g x)))
    (measure_lp_norm mu N 1 (partial_function_total g)).
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hPowerIntegral)=> x y.
  split.
  - move=> [v [hV hY]]; apply/real_total_integrand_graph.
    have hValue : g x=v := hV.
    rewrite -hValue in hY.
    by rewrite (real_power_one_exponent (real_seminorm_nonnegative hN.1 _)) in hY.
  - move/real_total_integrand_graph=> hY.
    exists (g x); split; first exact: erefl.
    by rewrite (real_power_one_exponent (real_seminorm_nonnegative hN.1 _)).
rewrite hNormFunction in hNormIntegral.
have hNormValue : measure_lp_norm mu N 1 (partial_function_total g)=(N z*a)%:E :=
  measure_integral_unique hNormIntegral hScale.
have hLpFinite : (measure_lp_norm mu N 1 (partial_function_total g)< +oo)%E.
  by rewrite hNormValue ltry.
have hOff (x : X) (y : real_norm_metric_space hN) :
    partial_function_graph (partial_function_total g) x y -> ~K x -> y=0.
  move=> hValue hx; have hGX : g x=y := hValue.
  rewrite -hGX /g.
  have hNotA : ~A x by move=> hAx; exact: hx (@hAK x hAx).
  by rewrite (characteristic_off_set hChi hNotA) scale0r.
have [f [hValue [_ [hFOff [_ hSize]]]]] :=
  @compact_summable_partial_field_representative R X V N hN mu hm
    (partial_function_total g) hMeas hLpFinite K hK hOff.
exists f; split.
- move=> x; exact: (@hValue x (g x) (erefl (g x))).
split; last exact: hFOff.
rewrite -hSize hNormValue hMu -EFinM.
reflexivity.
Qed.
End CompactCharacteristicField.
