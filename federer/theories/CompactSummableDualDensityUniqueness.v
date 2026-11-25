(** Federer (1969), 4.1.19, p. 377:
    almost uniqueness of the representing forms.
    The original Omega actions contain every
    compact continuous scalar probe times a
    coefficient vector. Scalar Radon uniqueness
    and the original finite basis identify the field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Bilinear Hom RealNormUP NormMetric LinearBasis Annihilator
  FiniteDualDimension
  ContinuousDualUP VectorDaniellHypotheses FunctionLatticeUP
  CompactSupportFunctionUP CompactContinuousVectorFields
  CompactContinuousVectorModule PartialFunctionBasic MeasureUP
  MeasureAlmostUP MeasurableFunctionUP MeasurableNormedFunctionUP
  CountablyMeasurableUP MeasureIntegralUP SummableRealFunctionUP
  RealLatticeDensityUP RadonMeasureUP RadonCompactScalarIntegral
  RadonLatticeLocalUniqueness LocallyNullMeasureUP LocallyAlmostMeasureLaws
  CountablyFiniteLocalNull CompactSummableFieldSealed CompactSummableFieldLaws
  CompactSummableFieldContinuous NormDualEvaluationMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactDualUniqueness.
Variable R : realType.
Variable X : topologicalType.
Variables V D : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Variable hSep : is_separable_normed_space hN.
Variable ed : Hom D (Hom V R^o).
Variable DN : D -> R.
Variable hDN : is_real_norm DN.
Variable hDual : is_continuous_dual hN ed DN.
Variable d : nat.
Variable e : 'I_d -> V.
Variable he : is_basis e.
Variable mu : set X -> \bar R.
Hypotheses (hm : is_measure mu) (hr : is_radon_measure mu).
Hypothesis hCountable : measure_countably_measurable mu setT.
Local Notation W := (@CompactSummableField.space R X V N hN mu hm).
Local Notation value := (@compact_summable_field_value R X V N hN mu hm).
Local Notation L :=
  (positive_function_lattice (@compactly_supported_continuous_functions R X)).
Variables a b : X -> D.
Hypothesis hA : is_measurable_normed_function mu
  (partial_function_total (fun x => (a x : real_norm_metric_space hDN))).
Hypothesis hB : is_measurable_normed_function mu
  (partial_function_total (fun x => (b x : real_norm_metric_space hDN))).
Hypothesis hAction : forall w : W, exists r : R,
  is_measure_integral mu (real_total_integrand (fun x => ed (a x) (value w x))) r%:E /\
  is_measure_integral mu (real_total_integrand (fun x => ed (b x) (value w x))) r%:E.

(** Source for [compact_summable_dual_density_almost_unique]:
    equality of both original Omega actions
    gives almost equality of the form fields,
    supporting Federer 4.1.19, p. 377.
    Finite coefficient dimension and the original
    countably measurable Radon domain suffice. No
    smoothness, normality or finite total measure is added. *)
Theorem compact_summable_dual_density_almost_unique :
  measure_almost_everywhere mu [set x | a x=b x].
Proof.
have hCoordinate (y : V) :
    measure_locally_almost_everywhere mu [set x | ed (a x) y=ed (b x) y].
  have hValues (f : X -> R) : exists r : R, L f ->
      is_measure_integral mu (real_total_integrand
        (fun x => f x*ed (a x) y)) r%:E /\
      is_measure_integral mu (real_total_integrand
        (fun x => f x*ed (b x) y)) r%:E.
    have [hF|hF] := pselect (L f).
    - have hVector := @vector_lattice_module_product R X V N hN
        (@compactly_supported_continuous_functions R X)
        (@compact_continuous_vector_fields R X V N hN)
        (@compact_continuous_vector_lattice_module R X V N hN) f y hF.1.
      have [w hW] := @compact_summable_continuous_field_representative R X V N hN
        hSep mu hm hr (fun x => f x*:y) hVector.
      have [r [hLeft hRight]] := hAction w.
      have hPair (c : X -> D) :
          (fun x => ed (c x) (value w x))=(fun x => f x*ed (c x) y).
        apply: funext=> x; rewrite (congr1 (fun g => g x) hW).
        exact: (linZ (hom_linear (ed (c x)))).
      exists r; move=> _.
      by rewrite (hPair a) in hLeft; rewrite (hPair b) in hRight; split.
    - exists 0; by move=> hFalse; exact: False_ind _ (hF hFalse).
  have [A hValuesA] := choice hValues.
  have hLeft : is_real_lattice_density mu L A (fun x => ed (a x) y).
    split.
    - exact: (@norm_dual_evaluation_measurable R X V D N hN ed DN
        hDN hDual mu hm a y hA).
    - move=> f hF; exact: (hValuesA f hF).1.
  have hRight : is_real_lattice_density mu L A (fun x => ed (b x) y).
    split.
    - exact: (@norm_dual_evaluation_measurable R X V D N hN ed DN
        hDN hDual mu hm b y hB).
    - move=> f hF; exact: (hValuesA f hF).2.
  exact: (@radon_compact_lattice_density_locally_unique R X mu hm hr
    (@radon_positive_compact_integral R X mu hm hr) A
    (fun x => ed (a x) y) (fun x => ed (b x) y)
    (@radon_positive_compact_integral_laws R X mu hm hr) hLeft hRight).
have hAll := @measure_locally_almost_countable R X [the choiceType of 'I_d]
  mu hm setT (fun i => [set x | ed (a x) (e i)=ed (b x) (e i)])
  (countableP _) (fun i _ => hCoordinate (e i)).
have hLocal : measure_locally_almost_everywhere mu [set x | a x=b x].
  apply: (@measure_locally_almost_mono R X mu hm _ _ _ hAll)=> x hx.
  apply: (continuous_dual_injective hDual); apply: hom_ext=> y.
  rewrite (@basis_vector_expansion R V d e he y) !linear_sum.
  apply: eq_bigr=> i _; rewrite !linearZ.
  exact: (congr1 (fun t : R^o => (dual_basis he i y : R)*:t) (hx i Logic.I)).
exact: (@countably_finite_locally_null_is_null R X mu hm _ hCountable hLocal).
Qed.
End CompactDualUniqueness.
