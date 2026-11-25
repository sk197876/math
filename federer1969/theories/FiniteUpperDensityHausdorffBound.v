(** Federer (1969), 3.3.15, p. 299: actual original
    Hausdorff mass bound on every positive upper-density stratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic BorelRegularMeasureUP TopologicalBorel
  FiniteBorelOpenInfimum MetricDensities HausdorffMeasure HausdorffSphericalComparison
  SphericalMetricDensityTheorems.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_upper_density_hausdorff_bound]: the original
    H^m(B)<=i*mu(B) comparison in Federer 3.3.15, p. 299, using
    2.10.19(3), p. 181. The actual finite measure's open-infimum
    law extends the printed Borel-source comparison to EVERY original
    B at a fixed positive upper-density threshold. No source
    measurability or supplied Radon approximation is assumed. *)
Theorem finite_upper_density_hausdorff_bound (R:realType) (X:metricType R) m
    (mu:set X->\bar R) (B:set X) (t:R):
  is_measure mu ->is_borel_regular_measure mu ->mu setT< +oo ->(0<t)%R ->
  (forall x,B x ->t%:E<upper_metric_density m mu x) ->
  @hausdorff_measure R X m B<=t^-1%R%:E*mu B.
Proof.
move=>hMu hRegular hFinite ht hDensity.
have hClosed S:closed S ->measure_measurable mu S.
  move=>hS; exact:(@borel_regular_borel_measurable R X mu hMu hRegular S (closed_borel_set hS)).
have hSpherical:t%:E*@spherical_measure R X m B<=mu B.
  apply:(@finite_borel_regular_open_infimum R X mu B
    (t%:E*@spherical_measure R X m B) hMu hRegular hFinite)=>V hV hBV.
  exact:(@federer_2_10_19_3 R X m mu B V t hMu hClosed hV hBV hDensity).
have hReciprocal:(0<=t^-1%R%:E)%E by rewrite lee_fin invr_ge0; exact:ltW ht.
have hBound:=lee_wpmul2l hReciprocal hSpherical.
rewrite muleA -EFinM mulVf ?gt_eqF // mul1e in hBound.
exact:le_trans (@hausdorff_measure_le_spherical_measure R X m B) hBound.
Qed.
