(** Federer (1969), 2.9.22, p. 167: extend the implication (3)=>(4) of
    2.9.20, pp. 165–166, to normed curves and the induced measures of every
    continuous dual scalarisation. The finite-family law gives relative norm
    continuity, and each bounded scalar evaluation preserves absolute
    continuity. Apply the already proved scalar induced-pair theorem. No
    relevant erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground ContinuousDualUP RealFunctionalNormUP
  CurveArcLength NormedBVInducedDerivates NormedCurveAbsoluteContinuityUP
  MetricCurveAbsoluteContinuityUP MetricCurveAbsoluteContinuityBasic
  RealAbsoluteContinuityUP AbsoluteContinuityInducedMeasures StieltjesImageMeasures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_absolute_continuity_induced_measures]: direct
    (3)=>(4) part of Federer 2.9.22, p. 167, extending 2.9.20, pp. 165–166
    Continuity is relative to the closed segment; both induced measures are
    restricted to its open interior. Every functional is treated separately,
    including the zero functional, without an uncountable intersection of
    almost-everywhere assertions. *)
Theorem normed_absolute_continuity_induced_measures (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> real_norm_metric_space hN) (a b : R) :
  curve_locally_finite_variation g -> is_absolutely_continuous_metric_curve g a b ->
  normed_curve_continuous_induced_measures hN ed g a b.
Proof.
move=> hg hAC; split; first exact: metric_absolute_continuity_continuous hAC.
move=> alpha psip psim hp.
have hNa := continuous_dual_norm_laws hD alpha.
have h0 := real_functional_norm_nonnegative hNa.
have hbound (x y : real_norm_metric_space hN) :
    mdist (ed alpha x : real_line_metric R) (ed alpha y)<=DN alpha*mdist x y.
  rewrite real_line_metric_distanceE real_norm_metric_distanceE.
  rewrite -(linearB (hom_as_linear (ed alpha)) x y) hom_as_linearE.
  exact: real_functional_norm_bound hNa (x-y).
have hMetric := @metric_absolute_continuity_lipschitz_postcomposition R
  [the metricType R of real_norm_metric_space hN] [the metricType R of real_line_metric R]
  (ed alpha) g (DN alpha) a b h0 hbound hAC.
have hReal := (@metric_absolute_continuity_real_agreement R (fun t => ed alpha (g t)) a b).1 hMetric.
have hScalarBV := @normed_bv_scalarisation R E D N hN ed DN hD g hg alpha.
have hInd := @real_absolute_continuity_induced_measures R (fun t => ed alpha (g t))
  psip psim a b hScalarBV hp hReal.
exact hInd.2.
Qed.
