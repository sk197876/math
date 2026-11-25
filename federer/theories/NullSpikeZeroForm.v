(** Federer (1969), 4.1.19, p. 377: a supporting
    test of the distinction between a measurable
    representative's essential comass and its literal
    pointwise global comass from 4.1.7, p. 358.
    The field is the existing singleton characteristic
    function viewed as an actual zero-form. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric
  GrassmannAbbreviations ExteriorGrading AlternatingForms AlternatingPairing PairingLinear
  CurrentCoefficientNorms CurrentZeroCovectorMaps
  CharacteristicFunctionUP CharacteristicFunctionSealed
  PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP
  MeasureAlmostBasic MeasureAlmostEquality MeasurableNormedFunctionUP
  MeasurableNormedBasic MeasureEssentialNormUP MeasureEssentialNorm
  MeasureIntegralUP MeasureConullZeroIntegral SummableRealFunctionUP
  CurrentGlobalComassUP CurrentGlobalComassSealed CurrentGlobalComassBound
  CurrentGlobalComassWitness NullSupportedFieldEssentialNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [null_spike_zero_form]: the singleton
    modification considered in the representative review
    of Federer 4.1.19, p. 377. Its definition
    reuses the opaque characteristic function of
    2.2.14, p. 70, and the original scalar
    zero-form identification of 1.4.1, p. 17. *)
Definition null_spike_zero_form (R : realType) n (a : R_n R n)
    (x : R_n R n) : A_m (R_n R n) R^o 0%N :=
  @current_scalar_zero_form R n
    (@CharacteristicFunction.value R (R_n R n) [set a] x).

Section NullSpikeZeroForm.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o 0%N).
Local Notation YN := (@current_form_comass R h2 n 0%N).
Local Notation hYN := (@current_form_comass_real_norm R h2 n 0%N).
Variable a : X.
Local Notation chi := (@CharacteristicFunction.value R X [set a]).
Local Notation hChi := (@CharacteristicFunction.laws R X [set a]).
Local Notation phi := (@null_spike_zero_form R n a).

(** Source for [null_spike_zero_form_at_point]: the
    test representative has scalar value one at
    its exceptional point, supporting the global
    comass review of 4.1.19, p. 377. *)
Lemma null_spike_zero_form_at_point :
  phi a = @current_scalar_zero_form R n 1.
Proof.
by rewrite /null_spike_zero_form (characteristic_on_set hChi (erefl a)).
Qed.

(** Source for [null_spike_zero_form_off_point]: the
    same representative is zero elsewhere, supporting
    the almost-uniqueness convention of 4.1.19, p. 377. *)
Lemma null_spike_zero_form_off_point x : x <> a -> phi x = 0.
Proof.
move=> hx.
by rewrite /null_spike_zero_form (characteristic_off_set hChi hx) linear0.
Qed.

(** Source for [null_spike_zero_form_global_comass]:
    the original global comass detects the
    exceptional point, by 4.1.7, p. 358.
    This is a representative-sensitivity test for
    the displayed norm formula in 4.1.19, p. 377. *)
Theorem null_spike_zero_form_global_comass :
  @CurrentGlobalComass.value R h2 n 0%N setT phi = 1%:E.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@current_global_comass_bound R h2 n 0%N setT phi 1).2.
  move=> x _.
  rewrite /null_spike_zero_form
    (@current_zero_form_coefficient_norm R h2 n)
    (@current_scalar_zero_form_inverse R n).
  case: (pselect (x=a)) => [hx|hx].
  + by rewrite (characteristic_on_set hChi hx) normr1.
  + by rewrite (characteristic_off_set hChi hx) normr0.
- have hLower := @current_global_comass_point_lower R h2 n 0%N setT phi a Logic.I.
  rewrite null_spike_zero_form_at_point
    (@current_zero_form_coefficient_norm R h2 n)
    (@current_scalar_zero_form_inverse R n) normr1 in hLower.
  exact: hLower.
Qed.

Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Hypothesis hNull : mu [set a] = 0%E.

(** Source for [null_spike_zero_form_almost_zero]:
    a null-point modification preserves the
    original almost-equality class, 2.3.1, p. 72,
    supporting measurable forms in 4.1.19, p. 377. *)
Theorem null_spike_zero_form_almost_zero :
  measure_almost_equal mu
    (partial_function_total (fun _ : X => (0 : real_norm_metric_space hYN)))
    (partial_function_total (fun x => (phi x : real_norm_metric_space hYN))).
Proof.
apply: (@measure_almost_equal_total R X (real_norm_metric_space hYN)
  mu (fun _ => 0) (fun x => phi x)).2.
apply: (@measure_null_subset R X mu hm _ [set a] _ hNull).
move=> x hBad; apply: contrapT => hx.
apply: hBad; exact: esym (null_spike_zero_form_off_point hx).
Qed.

(** Source for [null_spike_zero_form_measurable]:
    the actual singleton modification remains
    normed measurable by 2.3.8, p. 78,
    supporting the representative review of
    Federer 4.1.19, p. 377. *)
Theorem null_spike_zero_form_measurable :
  is_measurable_normed_function mu
    (partial_function_total (fun x => (phi x : real_norm_metric_space hYN))).
Proof.
apply: (@measurable_normed_almost_equal R X Y YN hYN mu hm
  (partial_function_total (fun _ => 0)) _ _
  null_spike_zero_form_almost_zero).
exact: (@measurable_normed_total_constant R X Y YN hYN mu hm 0).
Qed.

(** Source for [null_spike_zero_form_essential_comass]:
    the original essential seminorm ignores a
    null-point modification, 2.4.12, p. 86.
    This supplies the essential side of the
    representative review of 4.1.19, p. 377. *)
Theorem null_spike_zero_form_essential_comass :
  measure_essential_norm mu YN (partial_function_total phi) = 0%E.
Proof.
apply: (@null_supported_field_essential_norm R X Y mu hm YN phi [set a] hNull).
move=> x hx; rewrite (null_spike_zero_form_off_point hx).
exact: (real_seminorm_zero hYN.1).
Qed.

(** Source for [null_spike_zero_form_pairing_integral]:
    all original test pairings ignore the
    exceptional point, by 2.4.3, p. 82,
    supporting the two representation formulas
    and weak equation in 4.1.19, p. 377. *)
Theorem null_spike_zero_form_pairing_integral
    (xi : X -> exterior_power X 0%N) :
  is_measure_integral mu
    (real_total_integrand (fun x => pairing (xi x) (phi x))) 0%E.
Proof.
apply: (@measure_almost_zero_integral R X mu hm).
have hConull : measure_almost_everywhere mu (~` [set a]).
  by rewrite /measure_almost_everywhere setCK.
apply: (@measure_almost_everywhere_mono R X mu hm (~` [set a]) _ _ hConull).
move=> x hx; apply/real_total_integrand_graph.
change ((pairing_right (xi x) (phi x))%:E = 0%E).
by rewrite (null_spike_zero_form_off_point hx) linear0.
Qed.
End NullSpikeZeroForm.
