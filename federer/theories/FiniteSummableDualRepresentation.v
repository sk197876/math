(** Federer (1969), 4.1.19, p. 377: the
    finite-dimensional L1 dual representation on
    the original measure space. Scalar Radon
    duality supplies the coefficient densities, the
    original finite basis assembles the field,
    and the exact scalar norms give the sharp bound. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis
  ContinuousDualUP FiniteNormMetricPolish MeasureUP RadonMeasureUP
  CountablyMeasurableUP PartialFunctionBasic MeasurableNormedFunctionUP
  MeasureIntegralUP SummableRealFunctionUP VectorDaniellHypotheses
  SummableFieldSealed SummableFieldLaws SummableFunctionalComponentDensity
  SummableFiniteDualDensity SummableDualDensitySharpBound
  SummableDualBoundedRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [finite_summable_dual_representation]:
    apply the earlier scalar duality to the
    finite coefficient space, as in Federer
    4.1.19, p. 377. The representing
    field belongs to the actual normed dual,
    satisfies the original bound at every point,
    and represents every original raw L1 field.
    No finite total measure is imposed. *)
Theorem finite_summable_dual_representation
    (R : realType) (X : topologicalType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R) (hDN : is_real_norm DN)
    (hDual : is_continuous_dual hN ed DN)
    d (e : 'I_d -> V) (he : is_basis e)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu)
    (hCountable : measure_countably_measurable mu setT)
    (F : Hom (@SummableField.space R X V N hN mu hm) R^o)
    (c : R) :
  0 <= c ->
  (forall w, `|F w| <= c*@summable_field_size R X V N hN mu hm w) ->
  exists phi : X -> D,
    is_measurable_normed_function mu
      (partial_function_total (fun x => (phi x : real_norm_metric_space hDN))) /\
    (forall x, DN (phi x) <= c) /\
    forall w : @SummableField.space R X V N hN mu hm,
      is_measure_integral mu (real_total_integrand (fun x =>
        ed (phi x) (@summable_field_value R X V N hN mu hm w x))) (F w)%:E.
Proof.
move=> hC hBound.
have hSep : is_separable_normed_space hN.
  exact: (@finite_norm_metric_separable R V N hN d e he).
have [k hK] := @summable_functional_component_density_family R X V N hN
  mu hm hSep hr F c hC hBound.
have [phi [hPhi [[b [hB hPhiBound]] hAction]]] :=
  @summable_finite_dual_density_exists R X V D N hN ed DN hDN hDual
    d e he mu hm F c hC k hK.
have hSharp := @summable_dual_density_sharp_almost_bound R X V D N hN hSep
  ed DN hDN hDual mu hm hCountable F c hC hBound phi hPhi b hB
  hPhiBound hAction.
have [psi [hPsi [hPsiBound [hEqual hPsiAction]]]] :=
  @summable_dual_bounded_representative R X V D N hN ed DN hDN mu hm F
    phi c hC hPhi hSharp hAction.
exists psi; split; first exact: hPsi.
split; first exact: hPsiBound.
exact: hPsiAction.
Qed.
