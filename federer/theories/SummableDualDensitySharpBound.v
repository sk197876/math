(** Federer (1969), 4.1.19, p. 377: the
    assembled dual field has the sharp original
    L-infinity bound. Test each fixed coefficient
    direction by the existing scalar L1 duality,
    then use one countable dense family and
    the original actual dual-norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology RealFunctionalNormUP ContinuousDualUP
  VectorDaniellHypotheses MeasureUP MeasureAlmostUP MeasurableFunctionUP
  MeasurableNormedFunctionUP MeasurableTotalBasic BorelFunctionBasic
  CountablyMeasurableUP PartialFunctionBasic MeasureIntegralUP
  SummableRealFunctionUP TotalScalarLpUP TotalScalarLpFiniteSeminorm
  FunctionOperatorSeminorm TotalEssentialNormBound RealLatticeDensityUP
  LpConjugatePair LpFunctionalDensityUP LpFunctionalDensity
  SummableFieldSealed SummableFieldLaws SummableFieldLinearImage
  SummableFieldRepresentation SummableScalarFunctionalRepresentation
  BoundedScalarLoneDensity AlmostDenseDualBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SharpBound.
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
Variable mu : set X -> \bar R.
Hypothesis hm : is_measure mu.
Hypothesis hCountable : measure_countably_measurable mu setT.
Local Notation W := (@SummableField.space R X V N hN mu hm).
Local Notation S := (@SummableField.space R X R^o (fun t : R => `|t|%R)
  (scalar_absolute_value_norm R) mu hm).
Local Notation value := (@summable_field_value R X V N hN mu hm).
Local Notation size := (@summable_field_size R X V N hN mu hm).
Local Notation scalarValue := (@summable_field_value R X R^o
  (fun t : R => `|t|%R) (scalar_absolute_value_norm R) mu hm).
Local Notation scalarSize := (@summable_field_size R X R^o
  (fun t : R => `|t|%R) (scalar_absolute_value_norm R) mu hm).
Variable F : Hom W R^o.
Variable c : R.
Hypothesis hC : 0 <= c.
Hypothesis hBound : forall w, `|F w| <= c*size w.
Variable phi : X -> D.
Hypothesis hPhi : is_measurable_normed_function mu
  (partial_function_total (fun x => (phi x : real_norm_metric_space hDN))).
Variable b : R.
Hypothesis hB : 0 <= b.
Hypothesis hPhiBound : forall x, DN (phi x) <= b.
Hypothesis hAction : forall w : W, is_measure_integral mu
  (real_total_integrand (fun x => ed (phi x) (value w x))) (F w)%:E.

(** Source for [summable_dual_density_direction_bound]:
    each fixed-direction evaluation of the represented
    field has essential bound c N(y), supporting
    Federer 4.1.19, p. 377. The exact
    scalar density norm of 2.5.7, pp. 98–99,
    gives this sharper bound from the original
    functional, rather than from a coordinate estimate. *)
Theorem summable_dual_density_direction_bound (y : V) :
  measure_almost_everywhere mu [set x | `|ed (phi x) y| <= c*N y].
Proof.
have hY : 0 <= N y := real_seminorm_nonnegative hN.1 y.
have [J [hJValue hJSize]] := @summable_scalar_orbit_map_exists R X V N hN
  hSep mu hm y.
pose G := hom_comp F J.
have hGBound (f : S) : `|G f| <= (c*N y)*scalarSize f.
  rewrite /G hom_compE -mulrA.
  exact: (le_trans (hBound (J f)) (ler_wpM2l hC (hJSize f))).
have [A [hA [hLinear hABound]]] :=
  @summable_scalar_functional_total_extension R X mu hm G (c*N y) hGBound.
pose ky := fun x => ed (phi x) y.
have hEvalLinear : linear (fun d : D => ed d y).
  move=> a v w; by rewrite linearP hom_addE hom_scaleE.
pose eval := @HomMap R D R^o (fun d => ed d y)
  (introT (asboolP _) hEvalLinear).
have hEvalBound (d : D) : `|eval d| <= N y*DN d.
  rewrite mulrC.
  exact: (real_functional_norm_bound (continuous_dual_norm_laws hDual d) y).
have hEvalContinuous : continuous (fun d : real_norm_metric_space hDN =>
    (eval d : real_norm_metric_space (scalar_absolute_value_norm R))).
  apply: (@norm_bounded_linear_continuous R D R^o DN (fun t : R => `|t|%R)
    hDN (scalar_absolute_value_norm R) eval).
  by exists (N y); split.
have hMeas := @measurable_total_borel_postcomposition R X
  (real_norm_metric_space hDN)
  (real_norm_metric_space (scalar_absolute_value_norm R)) mu hm
  (fun x => (phi x : real_norm_metric_space hDN))
  (fun d => (eval d : real_norm_metric_space (scalar_absolute_value_norm R)))
  hPhi.1 (continuous_borel_function hEvalContinuous).
have hDensity : is_real_lattice_density mu (total_scalar_lp mu 1) A ky.
  split; first exact: hMeas.
  move=> f hf.
  have hMember := (@total_scalar_lp_finite_equivalence R X mu hm 1 f).1 hf.
  have [w [hValue hSize]] := @summable_total_field_representative R X R^o
    (fun t : R => `|t|%R) (scalar_absolute_value_norm R) mu hm f hMember.
  have hIntegral := hAction (J w).
  have hPair : (fun x => ed (phi x) (value (J w) x)) =
      (fun x => f x*ky x).
    apply: funext=> x; rewrite (hJValue w x).
    rewrite (linZ (hom_linear (ed (phi x)))).
    change (scalarValue w x*ed (phi x) y = f x*ky x).
    by rewrite (congr1 (fun g => g x) hValue).
  have hFunctional : A f = F (J w).
    have h := hA w.
    by rewrite hValue /G hom_compE in h.
  by rewrite hPair -hFunctional in hIntegral.
have hBPoint (x : X) : `|ky x| <= b*N y.
  have h := real_functional_norm_bound
    (continuous_dual_norm_laws hDual (phi x)) y.
  exact: (le_trans h (ler_wpM2r hY (@hPhiBound x))).
have hBY : 0 <= b*N y := mulr_ge0 hB hY.
have [hFull hOldNorm] := @bounded_scalar_lone_density_full R X mu hm
  hCountable A ky (b*N y) hBY hDensity hBPoint.
have hConjugate : is_lp_conjugate_pair (1 : \bar R) +oo.
  by right; left.
have hExact := @lp_functional_density_norm R X mu hm 1 +oo A ky
  hConjugate hFull.
have hCY : 0 <= c*N y := mulr_ge0 hC hY.
have hOperator := @function_operator_seminorm_least_bound R X
  (total_scalar_lp mu 1) A (finite_total_scalar_lp_norm mu 1) (c*N y)
  hCY hABound.
have hSharp : (total_scalar_lp_norm mu +oo ky <= (c*N y)%:E)%E.
  by rewrite hExact.
exact: (@total_essential_norm_almost_bound R X mu hm ky (c*N y)
  hFull.1 hSharp).
Qed.

(** Source for [summable_dual_density_sharp_almost_bound]:
    one conull set carries the exact actual
    dual bound c, supporting Federer 4.1.19,
    p. 377. The existing countable dense-family
    and least-dual-bound laws convert the scalar
    estimates without changing the coefficient norm. *)
Theorem summable_dual_density_sharp_almost_bound :
  measure_almost_everywhere mu [set x | DN (phi x) <= c].
Proof.
have [B [hCount hDense]] := hSep.
apply: (@almost_dense_dual_evaluation_bound R X V D N hN ed DN hDual
  B hCount hDense mu hm phi c hC)=> y _.
exact: summable_dual_density_direction_bound.
Qed.
End SharpBound.
