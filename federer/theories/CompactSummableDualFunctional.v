(** Federer (1969), 4.1.19, p. 377: a
    bounded measurable dual field acts linearly
    on the original compact L1 fields.
    Measurability and the sharp integral bound
    reuse the preceding bilinear and dominated-integral laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric
  ContinuousDualUP RealFunctionalNormUP VectorDaniellHypotheses
  NormBoundedBilinearUP PartialFunctionBasic MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasurableBoundedBilinearProduct TotalScalarMeasurability
  MeasureStepIntegralIdentification SummableRealFunctionUP SummableRealArithmetic
  VectorDaniellPairingMeasurability CompactSummableFieldSealed
  CompactSummableFieldLaws CompactSummableFieldIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [compact_summable_dual_functional_exists]:
    each bounded measurable form in the
    converse of Federer 4.1.19, p. 377,
    determines its linear Omega action with
    the same original L1 bound. Both the
    integral and the bound are proved, rather
    than assumed as laws of a selected functional. *)
Theorem compact_summable_dual_functional_exists (R : realType)
    (X : topologicalType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hDN : is_real_norm DN) (hDual : is_continuous_dual hN ed DN)
    (hSep : is_separable_normed_space hN)
    (hDSep : is_separable_normed_space hDN)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (phi : X -> D) (c : R) :
  0 <= c -> is_measurable_normed_function mu
    (partial_function_total (fun x => (phi x : real_norm_metric_space hDN))) ->
  (forall x, DN (phi x) <= c) ->
  exists F : Hom (@CompactSummableField.space R X V N hN mu hm) R^o,
    (forall w, is_measure_integral mu (real_total_integrand (fun x =>
      ed (phi x) (@compact_summable_field_value R X V N hN mu hm w x)))
      (F w)%:E) /\
    forall w, `|F w| <= c*@compact_summable_field_size R X V N hN mu hm w.
Proof.
move=> hC hPhi hCap.
pose W := @CompactSummableField.space R X V N hN mu hm.
pose value := @compact_summable_field_value R X V N hN mu hm.
pose size := @compact_summable_field_size R X V N hN mu hm.
have hBilinear : @norm_bounded_bilinear R V D R^o N DN (fun t : R^o => `|t|%R)
    (fun v d => ed d v).
  split.
  - split.
    + move=> d; exact: (hom_linear (ed d)).
    + move=> v a d e; by rewrite linearP hom_addE hom_scaleE.
  - exists 1; split; first exact: ler01.
    move=> v d; rewrite mul1r mulrC.
    exact: (real_functional_norm_bound (continuous_dual_norm_laws hDual d) v).
have hAt (w : W) : exists r : R,
    is_measure_integral mu
      (real_total_integrand (fun x => ed (phi x) (value w x))) r%:E /\
    `|r| <= c*size w.
  have hMeas := @measurable_bounded_bilinear_product R X V D R^o
    N DN (fun t : R => `|t|%R) hN hDN (scalar_absolute_value_norm R)
    mu hm (fun v d => ed d v) hBilinear (value w) phi hSep hDSep
    (@compact_summable_field_measurable R X V N hN mu hm w).1 hPhi.1.
  have hIntegrand := @measurable_partial_real_embedding R X mu hm _
    (@total_scalar_real_measurable R X mu hm _ hMeas).
  have hNormIntegral := @real_total_integral_scale R X mu hm
    (fun x => N (value w x)) (size w) c
    (@compact_summable_field_size_integral R X V N hN mu hm w).
  apply: (@real_total_dominated_integral R X mu hm
    (fun x => ed (phi x) (value w x)) (fun x => c*N (value w x))
    (c*size w) hIntegrand hNormIntegral)=> x.
  have hBound := real_functional_norm_bound
    (continuous_dual_norm_laws hDual (phi x)) (value w x).
  exact: (le_trans hBound (ler_wpM2r
    (real_seminorm_nonnegative hN.1 (value w x)) (hCap x))).
have [f hF] := choice hAt.
have hLinear : forall (a : R) (v w : W), f (a*:v+w)%R=a*f v+f w.
  move=> a v w.
  have hScaled := @real_total_integral_scale R X mu hm
    (fun x => ed (phi x) (value v x)) (f v) a (hF v).1.
  have hAdded := @real_total_integral_add R X mu hm
    (fun x => a*ed (phi x) (value v x))
    (fun x => ed (phi x) (value w x)) (a*f v) (f w) hScaled (hF w).1.
  have hActual := (hF (a*:v+w)%R).1.
  have hPoint : (fun x => ed (phi x) (value (a*:v+w)%R x))=
      (fun x => a*ed (phi x) (value v x)+ed (phi x) (value w x)).
    apply: funext=> x.
    rewrite /value compact_summable_field_value_add
      compact_summable_field_value_scale.
    exact: (hom_linear (ed (phi x)) a (value v x) (value w x)).
  rewrite hPoint in hActual.
  exact: (EFin_inj (measure_integral_unique hActual hAdded)).
exists (@HomMap R W R^o f (introT (asboolP _) hLinear)).
split.
- move=> w; exact: (hF w).1.
- move=> w; exact: (hF w).2.
Qed.
