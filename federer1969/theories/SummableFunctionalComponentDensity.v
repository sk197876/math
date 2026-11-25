(** Federer (1969), 4.1.19, p. 377: apply
    the scalar L1 duality to the
    components F(f y) of the full
    L1 extension. The bound is c times
    the actual coefficient norm of y, before
    the finite-dimensional dual field is assembled. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric MeasureUP RadonMeasureUP
  PartialFunctionBasic MeasurableFunctionUP MeasureIntegralUP
  SummableRealFunctionUP VectorDaniellHypotheses
  SummableFieldSealed SummableFieldLaws SummableFieldLinearImage
  SummableScalarFunctionalRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section ComponentDensity.
Variable R : realType.
Variable X : topologicalType.
Variable V : lmodType R.
Variable N : V -> R.
Variable hN : is_real_norm N.
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Local Notation W := (@SummableField.space R X V N hN mu hm).
Local Notation S := (@SummableField.space R X R^o
  (fun t : R => `|t|%R) (scalar_absolute_value_norm R) mu hm).
Local Notation value := (@summable_field_value R X V N hN mu hm).
Local Notation size := (@summable_field_size R X V N hN mu hm).
Local Notation scalarValue := (@summable_field_value R X R^o
  (fun t : R => `|t|%R) (scalar_absolute_value_norm R) mu hm).
Local Notation scalarSize := (@summable_field_size R X R^o
  (fun t : R => `|t|%R) (scalar_absolute_value_norm R) mu hm).

(** Source for [is_summable_functional_component_density]:
    the scalar coefficient densities used with
    2.5.9 in Federer 4.1.19, p. 377.
    Every asserted integral is finite and represents
    the original actual field f y. The
    pointwise cap retains the supplied functional bound. *)
Definition is_summable_functional_component_density
    (F : Hom W R^o) (c : R) (y : V) (k : X -> R) :=
  is_measure_measurable_function mu
    (partial_function_total (fun x =>
      (k x : real_norm_metric_space (scalar_absolute_value_norm R)))) /\
  (forall x, `|k x| <= c*N y) /\
  forall (f : S) (v : W),
    (forall x, value v x = scalarValue f x*:y) ->
    is_measure_integral mu
      (real_total_integrand (fun x => scalarValue f x*k x)) (F v)%:E.

(** Source for [summable_functional_component_density_exists]:
    scalar L1 duality supplies the component
    representing F(f y), supporting Federer 4.1.19,
    p. 377, through 2.5.10, p. 101.
    The coefficient norm N(y) is exact. The
    source Radon measure may be infinite. *)
Theorem summable_functional_component_density_exists
    (hSep : is_separable_normed_space hN) (hr : is_radon_measure mu)
    (F : Hom W R^o) (c : R) (hC : 0 <= c)
    (hBound : forall v, `|F v| <= c*size v) (y : V) :
  exists k : X -> R, is_summable_functional_component_density F c y k.
Proof.
have hY : 0 <= N y := real_seminorm_nonnegative hN.1 y.
have [J [hValues hSize]] := @summable_scalar_orbit_map_exists R X V N hN
  hSep mu hm y.
pose G := hom_comp F J.
have hG : forall f : S, `|G f| <= (c*N y)*scalarSize f.
  move=> f; rewrite /G hom_compE -mulrA.
  exact: (le_trans (hBound (J f)) (ler_wpM2l hC (hSize f))).
have hCY : 0 <= c*N y := mulr_ge0 hC hY.
have [k [hKMeas [hKBound hIntegral]]] :=
  @summable_scalar_radon_functional_representation R X mu hm hr G
    (c*N y) hCY hG.
exists k; split; first exact: hKMeas.
split; first exact: hKBound.
move=> f v hV.
have hEqual : J f = v.
  apply: (@summable_field_value_injective R X V N hN mu hm).
  apply: funext=> x.
  rewrite (hValues f x); exact: (esym (hV x)).
have h := hIntegral f.
by rewrite /G hom_compE hEqual in h.
Qed.

(** Source for [summable_functional_component_density_family]:
    choose the scalar density for each coefficient
    direction before the common conull-set step,
    as in 2.5.12, p. 104, supporting
    Federer 4.1.19, p. 377. This
    existence theorem exposes no chosen family implementation. *)
Theorem summable_functional_component_density_family
    (hSep : is_separable_normed_space hN) (hr : is_radon_measure mu)
    (F : Hom W R^o) (c : R) (hC : 0 <= c)
    (hBound : forall v, `|F v| <= c*size v) :
  exists k : V -> X -> R,
    forall y, is_summable_functional_component_density F c y (k y).
Proof.
have hEach (y : V) :=
  @summable_functional_component_density_exists hSep hr F c hC hBound y.
have [k hK] := choice hEach.
by exists k.
Qed.
End ComponentDensity.
