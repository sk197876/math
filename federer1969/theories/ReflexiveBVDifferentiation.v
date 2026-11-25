(** Federer (1969), 2.9.22, pp. 167–168: actual norm differentiation almost
    everywhere for locally BV curves in a reflexive Banach space. The proof
    follows g=H o s, strong differentiation of the Lipschitz factor, the
    weighted null-preimage conclusion for s, and the two printed pointwise
    alternatives. No relevant erratum entry applies. Full variation and
    absolute-continuity conclusions extending 2.9.19–2.9.20 are separate
    from this existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP
  ContinuousDualUP ContinuousDualNorm ContinuousBidualUP CurveArcLength CurveBanachExtension
  NormedCurveDerivativeUP NormedDerivativeDualEvaluation NormedBVPointwiseReduction
  ReflexiveLipschitzDifferentiation MonotoneStieltjesDifferentiation MonotoneNullPreimageDerivative
  RealCurveDerivativeUP MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reflexive_bv_derivative_ae]: direct central
    norm-limit existence and simultaneous dual characterisation in
    Federer 2.9.22, pp. 167–168. Completeness gives the actual
    Banach extension H. The exceptional set where H has no norm
    derivative has zero weighted preimage; there s'=0 almost
    everywhere and the distance estimate gives g'=0. Elsewhere
    the actual norm chain rule applies. Ordinary null-preimage
    preservation is not assumed. No separability hypothesis is added. *)
Theorem reflexive_bv_derivative_ae (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> real_norm_metric_space hN) :
  is_complete_metric_space (real_norm_metric_space hN) ->
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v /\
      forall alpha, has_real_curve_derivative (fun t => ed alpha (g t)) x (ed alpha v)].
Proof.
move=> hY ht hr hg.
have [H hH] := @curve_banach_extension_exists R E N hN hY g hg.
have hLip (t u : R) : N (H t-H u)<=1 * `|t-u|.
  rewrite mul1r; exact (@curve_banach_extension_lipschitz_one R E N hN g hg H hH t u).
have hAEH := @reflexive_lipschitz_derivative_ae R E D B N hN ed DN hD eb BN hB
  tau H 1 ht hr ler01 hLip.
pose P : set (real_line_metric R) := [set z | exists v : E, has_normed_curve_derivative N H z v].
have hP : measure_almost_everywhere (@lebesgue_scalar_measure R) P.
  apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ _ hAEH)=> z [v [hv _]]; by exists v.
have hs (a b : R) : a<=b -> arc_length g a<=arc_length g b :=
  @arc_length_monotone R [the metricType R of real_norm_metric_space hN] g hg a b.
have hZero := @monotone_null_preimage_zero_derivative R (arc_length g) (~` P) hs hP.
have hS := @monotone_real_derivative_exists_ae R (arc_length g) hs.
have hall := measure_almost_everywhere_and (lebesgue_scalar_is_measure R) hZero hS.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ hall)=> x [hBad [w [hw hsx]]].
have [v hv] : exists v : E, has_normed_curve_derivative N g x v.
  case: (pselect (P (arc_length g x)))=> [[u hu]|hMissing].
  - exists (w *: u); exact (@normed_bv_factor_derivative R E N hN g H x w u hH hsx hu).
  - exists 0; exact (@normed_bv_zero_arc_derivative R E N hN g x hg (hBad hMissing)).
exists v; split=> //.
exact (@normed_curve_derivative_dual_evaluation R E D N hN ed DN hD g x v hv).
Qed.
