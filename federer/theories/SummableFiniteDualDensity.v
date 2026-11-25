(** Federer (1969), 4.1.19, p. 377: assemble
    the scalar coefficient densities into a
    bounded measurable field in the actual finite
    coefficient dual. The original basis, pairing
    and raw L1 fields are retained.
    The sharp bound is proved in a separate conull-set step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear Hom RealNormUP NormMetric RealMetricBackground
  LinearBasis FiniteDualDimension Biorthogonal RealFunctionalNormUP
  ContinuousDualUP ContinuousDualNorm FiniteContinuousDualBasis
  FiniteNormMetricPolish FiniteCoordinateMeasurability
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasurableNormedFunctionUP
  MeasurableTotalBasic ScalarNormExtendedEmbedding BorelFunctionBasic
  SeparableTargetNormedMeasurability MeasureIntegralUP SummableRealFunctionUP
  FiniteSignedRealIntegral SummableFieldSealed SummableFieldLaws
  SummableFunctionalComponentDensity SummableFiniteBasisDecomposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [summable_finite_dual_density_exists]:
    the finite coefficient assembly for the
    bounded differential forms in Federer 4.1.19,
    p. 377. This supporting theorem consumes
    the already represented scalar components. It
    returns their actual normed measurability, a
    finite pointwise norm bound and every original
    L1 pairing integral, with no whole-source finiteness premise. *)
Theorem summable_finite_dual_density_exists
    (R : realType) (X : topologicalType) (V D : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R) (hDN : is_real_norm DN)
    (hDual : is_continuous_dual hN ed DN)
    d (e : 'I_d -> V) (he : is_basis e)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F : Hom (@SummableField.space R X V N hN mu hm) R^o)
    (c : R) (hC : 0 <= c) (k : V -> X -> R)
    (hK : forall y,
      @is_summable_functional_component_density R X V N hN mu hm
        F c y (k y)) :
  exists phi : X -> D,
    is_measurable_normed_function mu
      (partial_function_total (fun x => (phi x : real_norm_metric_space hDN))) /\
    (exists b : R, 0 <= b /\ forall x, DN (phi x) <= b) /\
    forall w : @SummableField.space R X V N hN mu hm,
      is_measure_integral mu (real_total_integrand (fun x =>
        ed (phi x) (@summable_field_value R X V N hN mu hm w x))) (F w)%:E.
Proof.
pose W := @SummableField.space R X V N hN mu hm.
pose value := @summable_field_value R X V N hN mu hm.
pose scalarValue := @summable_field_value R X R^o (fun t : R => `|t|%R)
  (scalar_absolute_value_norm R) mu hm.
have [b [hb hDualBasis]] :=
  @finite_continuous_dual_basis_exists R V D N hN ed DN hDual d e he.
pose phi (x : X) : D := \sum_i k (e i) x*:b i.
have hCoordinate (i : 'I_d) (x : X) :
    dual_basis hb i (phi x) = k (e i) x.
  apply: (@biorthogonal_sum R D [the finType of 'I_d]
    (dual_basis hb) b).
  by move=> j l; rewrite dual_basisE eq_sym.
have hCoordinates (i : 'I_d) : is_measure_measurable_function mu
    (partial_function_total (fun x =>
      ((dual_basis hb i (phi x):R) : real_line_metric R))).
  have hValues : (fun x => ((dual_basis hb i (phi x):R) : real_line_metric R)) =
      (fun x => (k (e i) x : real_line_metric R)).
    apply: funext=> x; exact: hCoordinate.
  rewrite hValues.
  exact: (@measurable_total_borel_postcomposition R X
    (real_norm_metric_space (scalar_absolute_value_norm R)) (real_line_metric R)
    mu hm (fun x => (k (e i) x : real_norm_metric_space
      (scalar_absolute_value_norm R))) (fun s => (s : real_line_metric R))
    (hK (e i)).1
    (continuous_borel_function (@scalar_norm_real_identity_continuous R))).
have hMeas := @finite_coordinate_field_measurable R X D DN hDN d b hb
  mu hm phi hCoordinates.
have [B [hCount hDense]] := @finite_norm_metric_separable R D DN hDN d b hb.
have hNormed := @separable_target_measurable_normed R X D DN hDN B mu hm
  (partial_function_total phi) hCount hDense hMeas.
pose cap := \sum_i (c*N (e i))*DN (b i).
have hCapNonnegative : 0 <= cap.
  apply: sumr_ge0=> i _.
  apply: mulr_ge0; last exact: real_seminorm_nonnegative hDN.1 _.
  exact: mulr_ge0 hC (real_seminorm_nonnegative hN.1 _).
have hCap (x : X) : DN (phi x) <= cap.
  apply: (le_trans (real_seminorm_sum hDN.1 _) _).
  apply: ler_sum=> i _.
  rewrite (real_seminorm_scale hDN.1).
  exact: (ler_wpM2r (real_seminorm_nonnegative hDN.1 (b i))
    ((hK (e i)).2.1 x)).
have [C [J [hCoordinatesValue [hProducts hDecomposition]]]] :=
  @summable_finite_basis_decomposition R X V N hN mu hm d e he.
exists phi; split; first exact: hNormed.
split.
- exists cap; split; first exact: hCapNonnegative.
  exact: hCap.
move=> w.
have hTerm (i : 'I_d) : is_measure_integral mu
    (real_total_integrand (fun x => scalarValue (C i w) x*k (e i) x))
    (F (J i (C i w)))%:E.
  exact: ((hK (e i)).2.2 (C i w) (J i (C i w)) (hProducts i (C i w))).
have hSum := @finite_signed_real_sum_integral R X [the eqType of 'I_d]
  mu hm (index_enum 'I_d)
  (fun i x => (scalarValue (C i w) x*k (e i) x : real_line_metric R))
  (fun i => F (J i (C i w))) (fun i _ => hTerm i).
have hSumValue : (\sum_i F (J i (C i w))) = F w.
  by rewrite -linear_sum -(hDecomposition w).
have hPair (x : X) : ed (phi x) (value w x) =
    \sum_i scalarValue (C i w) x*k (e i) x.
  rewrite /phi linear_sum hom_sumE.
  apply: eq_bigr=> i _.
  change (ed (k (e i) x*:b i) (value w x) =
    scalarValue (C i w) x*k (e i) x).
  rewrite (linZ (hom_linear ed)) hom_scaleE (hDualBasis i).
  change (k (e i) x*dual_basis he i (value w x) =
    scalarValue (C i w) x*k (e i) x).
  by rewrite /scalarValue /value (hCoordinatesValue i w x) mulrC.
have hPairField : (fun x => ed (phi x) (value w x)) =
    (fun x => \sum_i scalarValue (C i w) x*k (e i) x).
  apply: funext=> x; exact: hPair.
rewrite /value in hPairField.
rewrite hPairField.
rewrite hSumValue in hSum; exact: hSum.
Qed.
