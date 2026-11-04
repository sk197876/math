(** Federer (1969), 3.2.46, pp. 281–282: the
    local volume bounds identify the full measure with
    integration of the continuous positive density. This
    supporting localisation theorem uses only earlier measure
    and Borel partition laws, with arbitrary outer test sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureAlmostBasic BorelRegularMeasureUP RegularMeasureUP
  MeasureDensityUP MeasureDensity MeasureDensityCover MeasureDensityMeasurable
  NonnegativeDensitySetLowerBound NonnegativeDensitySetUpperBound
  CountableOpenBaseUP TopologicalBorel BorelFamilyBasic
  MeasureLocalOpenComparison ContinuousPositiveRelativeControl LocalDensityComparisonAlgebra
  ExtendedPowerGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measure_continuous_local_density]: the
    full density identification from local lambda^k volume
    comparisons, expanding 3.2.46, pp. 281–282. The
    continuous density is actual; local comparison assumptions
    are independent estimates, not the desired integral law.
    No finiteness or measurability of test sets is required. *)
Theorem measure_continuous_local_density (R : realType) (X : topologicalType)
    (phi mu : set X -> \bar R) (U : nat -> set X)
    (h : X -> real_line_metric R) k :
  is_measure phi -> is_measure mu -> is_countable_open_base U ->
  is_regular_measure phi ->
  (forall B, borel_set B -> measure_measurable phi B /\ measure_measurable mu B) ->
  continuous h -> (forall x, 0<h x) ->
  (forall (lambda : R), 1<lambda -> forall a, exists V : set X,
    open V /\ V a /\ forall S, S `<=` V ->
      ((h a)%:E*phi S<=(lambda^+k)%:E*mu S)%E /\
      (mu S<=(lambda^+k)%:E*(h a)%:E*phi S)%E) ->
  is_measure_density phi (partial_function_total (fun x=>(h x)%:E : extended_real_line R)) mu.
Proof.
move=> hPhi hMu hBase hRegular hBorel hCont hPositive hLocal.
pose w := fun x=>(h x)%:E : extended_real_line R.
pose nu := measure_with_density phi (partial_function_total w).
have hDensity := measure_with_density_laws phi (partial_function_total w).
have hW x : (0<=w x)%E by rewrite /w lee_fin; exact: ltW (hPositive x).
have hNonnegative : measure_almost_everywhere phi
    (partial_extended_nonnegative_locus (partial_function_total w)).
  apply: (@measure_almost_everywhere_mono R X phi hPhi setT _ _
    (measure_almost_everywhere_true hPhi))=> x _.
  exists (w x); by split.
have hNu : is_measure nu := @measure_density_is_measure R X phi nu hPhi
  (partial_function_total w) hDensity hNonnegative.
have hNuBorel B (hB : borel_set B) : measure_measurable nu B.
  exact (@measure_density_preserves_measurable_sets R X phi nu hPhi
    (partial_function_total w) B hDensity hNonnegative (hBorel B hB).1).
have hCombined (lambda : R) (hLambda : 1<lambda) a :
    exists V : set X, open V /\ V a /\ forall S, S `<=` V ->
      (mu S<=(lambda^+k.+1)%:E*nu S)%E /\
      (nu S<=(lambda^+k.+1)%:E*mu S)%E.
  have hLambda0 : 0<lambda := lt_trans ltr01 hLambda.
  have [V [hV [hVa hVolume]]] := hLocal lambda hLambda a.
  have [W [hWOpen [hWa hControl]]] :=
    continuous_positive_relative_neighbourhood hCont (hPositive a) hLambda.
  exists (V `&` W); split; first exact: openI hV hWOpen; split; first by split.
  move=> S hS.
  have hSV : S `<=` V by move=> x hx; exact: (hS x hx).1.
  have hSW : S `<=` W by move=> x hx; exact: (hS x hx).2.
  have hVolumeS := hVolume S hSV.
  have hLower : (((h a/lambda)%:E)*phi S<=nu S)%E.
    apply: (@nonnegative_density_set_lower_bound R X phi nu hPhi w S (h a/lambda)
      hDensity hW); first by rewrite divr_gt0.
    move=> x hx; rewrite /w lee_fin; exact: (hControl x (hSW x hx)).1.
  have hUpper : (nu S<=((lambda*h a)%:E)*phi S)%E.
    apply: (@nonnegative_density_set_upper_bound R X phi nu hPhi w S (lambda*h a)
      hRegular hDensity); first exact: mulr_gt0 hLambda0 (hPositive a).
    move=> x hx; rewrite /w lee_fin; exact: (hControl x (hSW x hx)).2.
  exact: local_density_comparison_algebra hLambda0 hVolumeS.1 hVolumeS.2 hLower hUpper.
have hGlobal (lambda : R) (hLambda : 1<lambda) S :
    (mu S<=(lambda^+k.+1)%:E*nu S)%E /\
    (nu S<=(lambda^+k.+1)%:E*mu S)%E.
  have hPower : 0<=lambda^+k.+1 by apply: exprn_ge0; exact: ltW (lt_trans ltr01 hLambda).
  split.
  - apply: (@measure_local_open_comparison R X mu nu U _ hMu hNu hBase hPower).
    + move=> B hB; split; [exact: (hBorel B hB).2 | exact: hNuBorel B hB].
    + move=> a; have [V [hV [ha hC]]] := hCombined lambda hLambda a.
      exists V; split; first exact hV; split; first exact ha.
      move=> B hB; exact: (hC B hB).1.
  - apply: (@measure_local_open_comparison R X nu mu U _ hNu hMu hBase hPower).
    + move=> B hB; split; [exact: hNuBorel B hB | exact: (hBorel B hB).2].
    + move=> a; have [V [hV [ha hC]]] := hCombined lambda hLambda a.
      exists V; split; first exact hV; split; first exact ha.
      move=> B hB; exact: (hC B hB).2.
have hEqual : mu=nu.
  apply: funext=> S; apply/eqP; rewrite eq_le; apply/andP; split.
  - apply: (@extended_power_geometric_squeeze R (nu S) (mu S) k.+1
      (measure_nonnegative hNu S))=> lambda hLambda.
    exact: (hGlobal lambda hLambda S).1.
  - apply: (@extended_power_geometric_squeeze R (mu S) (nu S) k.+1
      (measure_nonnegative hMu S))=> lambda hLambda.
    exact: (hGlobal lambda hLambda S).2.
rewrite hEqual; exact hDensity.
Qed.
