(** Federer (1969), 2.9.22, pp. 167–168: remove the separable-target
    restriction from the Lipschitz argument by the closed separable span of
    the curve image and closed-subspace reflexivity. The locally BV
    reduction through the arc-length parameter is separate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP NormMetric RealMetricBackground
  NormedSubspace SubspaceNormSeparability CurveArcLength LipschitzCurveVariation
  ClosedLinearSpanUP CurveSeparableLinearEnvelope ContinuousDualUP ContinuousDualNorm ContinuousDualSealed
  ContinuousBidualUP ContinuousBidualSealed ClosedSubspaceReflexivity
  MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure RealCurveDerivativeUP
  NormedCurveDerivativeUP NormedDerivativeDualEvaluation SeparableReflexiveLipschitzDifferentiation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [reflexive_lipschitz_derivative_ae]: direct full
    Lipschitz special case of Federer 2.9.22, pp. 167–168,
    including the printed arbitrary-target separability reduction.
    The closed separable span of im(g) inherits reflexivity
    by the proved Hahn–Banach argument. Sealed duals supply
    its abstract pairings, the separable theorem gives actual
    norm derivatives, and isometric inclusion returns them to Y.
    One conull set has the norm bound and every scalar dual
    identity. The general locally BV case is not claimed here. *)
Theorem reflexive_lipschitz_derivative_ae (R : realType)
    (E D B : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B) (g : R -> E) (L : R) :
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau -> 0<=L ->
  (forall t u, N (g t-g u)<=L * `|t-u|) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists w : E, has_normed_curve_derivative N g x w /\ N w<=L /\
      forall alpha, has_real_curve_derivative (fun t => ed alpha (g t)) x (ed alpha w)].
Proof.
move=> ht hr hL hg.
have hLip : forall t u, mdist (g t : real_norm_metric_space hN) (g u)<=L * `|t-u| := hg.
have hfin := @lipschitz_curve_locally_finite_variation R
  [the metricType R of real_norm_metric_space hN] g L hLip.
have [Z [hZclosed [hZimage hZsep]]] := @curve_separable_linear_envelope R E N hN g hfin.
have hZg t : Z (g t) by apply: hZimage; exists t.
pose W := [the lmodType R of subspace_space Z].
pose WN := subspace_norm N Z.
pose hW := subspace_norm_laws hN Z.
pose gZ t : W := @subspace_lift R E Z (g t) (hZg t).
pose F := @ContinuousDual.space R W WN hW.
pose ef := @ContinuousDual.evaluation R W WN hW.
pose FN := @ContinuousDual.norm R W WN hW.
have hF := @ContinuousDual.laws R W WN hW.
pose hFN := continuous_dual_norm_is_norm hF.
pose U := @ContinuousDual.space R F FN hFN.
pose eu := @ContinuousDual.evaluation R F FN hFN.
pose UN := @ContinuousDual.norm R F FN hFN.
have hU := @ContinuousDual.laws R F FN hFN.
pose sigma := @ContinuousBidual.value R W F U WN hW ef FN hF eu UN hU.
have hs := @ContinuousBidual.laws R W F U WN hW ef FN hF eu UN hU.
have hRefZ := @closed_subspace_reflexive R E D B F U N hN Z ed DN hD eb BN hB
  tau ef FN hF eu UN hU sigma ht hr hZclosed hs.
have [C [hCc hCd]] := @subspace_norm_separable R E N hN Z hZsep.
have hLipZ t u : WN (gZ t-gZ u)<=L * `|t-u|.
  change (N (g t-g u)<=L * `|t-u|); exact: hg.
have hAE := @separable_reflexive_lipschitz_derivative_ae R W F U WN hW ef FN hF eu UN hU
  sigma gZ L C hs hRefZ hCc hCd hL hLipZ.
apply: (@measure_almost_everywhere_mono R (real_line_metric R)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _ hAE)=> x [w [hw [hbound _]]].
have hd := @subspace_norm_derivative_inclusion R E N hN Z gZ x w hw.
have he : (fun t => subspace_val (gZ t))=g by apply/funext=> t; exact: subspace_liftE.
rewrite he in hd.
exists (subspace_val w); split=> //; split; first exact hbound.
exact (@normed_curve_derivative_dual_evaluation R E D N hN ed DN hD g x (subspace_val w) hd).
Qed.
